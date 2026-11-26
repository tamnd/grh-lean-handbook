---
title: Exercises and notes
lean:
  - New/Reduction/MainInequality.lean
  - New/Reduction/OneSidedBound.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

1. Let $b \geq 3$ and $\log b \geq 128$. Show that $8 f a \log^4 b + 40 \log(1 + 2b^2) f a \log^3 b \leq f a \log^5 b$. *Hint.* $\log(1 + 2b^2) \leq \log 3 + 2 \log b \leq 3 \log b$.

2. In the proof of the main inequality, replace the bound $n \geq (1 - 4/b^2) d_T$ by $n \geq (1 - \omega) d_T$ with $0 \leq \omega < 1$. Show that $m \cdot \mathrm{rem} \leq \mathrm{err}/(1 - \omega)$. Which step breaks if $\omega = 1$? *Hint.* Step 8 uses only $d_T \leq n/(1 - \omega)$ and $n > 0$.

3. Show by an example that Step 7 fails without $\mathrm{main} + \mathrm{loss} \geq 0$: find $n < d_T$ and $h < 0$ with $n h > d_T h$. Then explain how the compact edition replaces this sign condition. *Hint.* Section 3, the remark on the two editions.

4. Let $q = 3$ be the modulus of $\chi$ in the half-plane theorem. Compute $q_0 = 18480 q$, $\varphi(q_0)$ and $d_0 = 9240 q - 1$. Show that $d_0 \equiv 7 \pmod 8$ and that $d_0$ is prime to $q_0$, but that $d_0 = 27719 = 53 \cdot 523$ is not prime. Explain why the proof of the half-plane theorem does not need $d_0$ to be prime. Find the least prime $d \equiv d_0 \pmod{q_0}$. *Hint.* $\varphi(55440) = 8 \cdot 6 \cdot 4 \cdot 6 \cdot 10$. The criterion quantifies over the primes of the class. The least such prime is $27719 + 2 \cdot 55440$.

5. Show that the lemma $\lfloor y \rfloor^u \leq 2 y^u$ fails for $u = -2$ and $y = 2.9$. Prove that $\lfloor y \rfloor^u \leq 2^{-u} y^u$ for all $y \geq 2$ and $u \leq 0$. *Hint.* $y/2 \leq \lfloor y \rfloor$.

6. Suppose a proof gave $R^{(d)}_{q_0}(y) \leq y^{-\theta + \eta}$ for large $y$, for every prime $d \equiv d_0 \pmod{q_0}$ and every $\eta > 0$, with some $\theta > 1/2$. Suppose also that the criterion held for every $\beta > 0$ (the source proves it only for $\beta > 1/2$). Use this criterion and the factorization $L(s, \psi_0) = \zeta(s) \prod_{p \mid q_0} (1 - p^{-s})$ to show that $\zeta$ has no zero with $\operatorname{Re} s > 1 - \theta$. Why does this contradict Hardy's theorem? *Hint.* Take $\beta$ between $1 - \theta$ and $1/2$.

7. In the proof of the bound at integers, the term $x^{-2}$ comes from $B \geq 24/\varepsilon$. Which $B$ gives $x^{-10}$? Does the final exponent $-1/2 + 6\varepsilon$ change? *Hint.* Section 7.

## Notes and references

**Sources of this chapter.** The chapter follows the readable edition: New/Reduction/MainInequality.lean, New/Reduction/OneSidedBound.lean and New/Reduction/Zeros/PrimeNumberTheorem.lean. The budget of errors in Section 3 is from the head of New/Main.lean of the compact edition, lines 26 to 115. Findings F-113 and F-114 of the register of Volume 0 compare the two editions: the compact edition has the bound $x^{8\varepsilon - 1/2}$, takes $\varepsilon = (\min(\operatorname{Re} \rho, 1) - 1/2)/51$ in its proof of GRH, and replaces the prime number theorem by a window argument (`IsPolar.exists_window_sub_mul_le` (grh-compact)). Finding F-015 records the choice $q_0 = 18480 q$, $d_0 = 9240 q - 1$ in `New.grh`, where $q$ is the modulus of $\chi$. Finding F-081 records that Theorem C is used once, in the main inequality.

**The prime number theorem.** The source cites H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*, Cambridge University Press, 2007: Corollary 11.19 for the prime number theorem in progressions with a saving of every power of the logarithm, Chapter 11 for the zero-free region, and Section 6.2 for the passage from a zero-free region to an error term. The source lists these places as compared and confirmed. The Tauberian argument with one Taylor coefficient, in place of a contour integral, is the source's own form.

**Landau's criterion.** The criterion goes back to E. Landau, Über einen Satz von Tschebyschef, *Mathematische Annalen* 61 (1905). The source compares it with Montgomery and Vaughan, Sections 15.1 and 15.2, and with M. Suzuki, On variants of Chebyshev's conjecture, arXiv:2411.07436 (2024). [Landau's criterion](/chapter/landau-criterion/) gives the details.

**Earlier methods.** The head of MainInequality.lean names earlier work that bounds sums over primes by size against divisibility: I. E. Pritsker, The Gelfond-Schnirelman method in prime number theory (2005); A. Granville and H. M. Stark, ABC implies no "Siegel zeros" for $L$-functions of characters with negative discriminant (2000); E. Bombieri, Counting points on curves over finite fields, Séminaire Bourbaki 430 (1973); M. van Frankenhuijsen, The Riemann hypothesis for function fields over a finite field (2008). The source gives these as background. This book has not checked the places in them.

**Hardy's theorem.** G. H. Hardy, Sur les zéros de la fonction $\zeta(s)$ de Riemann, *Comptes Rendus de l'Académie des Sciences Paris* 158 (1914), proves that $\zeta$ has infinitely many zeros on the line $\operatorname{Re} s = 1/2$. Section 7 uses it only to show that no correct form of the method can save more than $x^{-1/2}$.

**Open questions.** Why $m \approx \sqrt{x}$, and which condition of the data stops a larger $m$, is open question Q-10 of the register (Section 7).

**Corrections to the notes.** Two small points differ from the research note of this part. First, the proof of `New.grh` does not use that the Euler factors $1 - \chi(p) p^{-\rho}$ are nonzero; it uses only that a nonzero product has nonzero factors (Section 6). Second, the data have $x_1 = \lfloor \exp(x^{\varepsilon/6}) \rfloor$, not $\exp(x^{\varepsilon/6})$, and the one-sided bound uses only $\log x_1 \geq x^{\varepsilon/12}$.

Status: drafted by a model. No person has checked this chapter against the Lean source.
