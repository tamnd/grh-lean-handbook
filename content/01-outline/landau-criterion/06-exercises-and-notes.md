---
title: Exercises
lean:
  - New/Reduction/Zeros/Criterion.lean
  - Lib/Analytic/Landau.lean
  - Lib/Analytic/QuadraticTwist.lean
  - New/Reduction/OneSidedBound.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $R$ be the remainder of the model criterion in Section 2. Assume the Riemann hypothesis. Prove that $R(x) = O(x^{-1/2}\log^2 x)$, and so that $R(x) \leq x^{\beta - 1}$ for all large $x$, for every $\beta > 1/2$. Together with the model criterion, this shows that the Riemann hypothesis is equivalent to the statement: $R(x) \leq x^{\beta - 1}$ for all large $x$, for every $\beta > 1/2$.

*Hint.* Under the Riemann hypothesis, $\psi(x) = x + O(x^{1/2}\log^2 x)$ (von Koch). The prime number theorem gives $R(x) \to 0$, so $R(x) = -\int_x^\infty (\psi(t) - t)\, t^{-2}\, dt$. Insert the bound and integrate.

**Exercise 2.** Let $0 < \beta < 1$. Suppose that $\psi(x) - x \geq -x^\beta$ for all large $x$. Prove that $\zeta(s) \neq 0$ for $\operatorname{Re} s > \beta$, with no hypothesis on real zeros. Then explain why the upper bound $\psi(x) - x \leq x^\beta$ does not give the same conclusion by this method, and compare with the remainder $R$ of Section 2.

*Hint.* The measure $(K e^{\beta v} + \psi(e^v) - e^v)\, dv$ on $v > 0$ is positive for a suitable $K$. Its transform is $K/(s - \beta)$ plus the transform of $\psi(x) - x$ in Section 2, and the residues of that transform at real zeros are $-\operatorname{ord}_\sigma \zeta/\sigma \leq 0$. Section 2 shows that an upper bound for $R$ is a lower bound for $\psi(t) - t$ on average.

**Exercise 3.** Let $q = 1$, let $d \equiv 7 \bmod 8$ be prime, and let $\zeta_K = \zeta \cdot L(\cdot, \chi_K)$ be the Dedekind zeta function of $K = \mathbb{Q}(\sqrt{-d})$. Show that the Dirichlet series of $\lambda = \Lambda(1 - \chi_K)$ is $-2\zeta'/\zeta + \zeta_K'/\zeta_K$. Deduce that the residue of the transform of $R_1$ at $\rho \neq 0, 1$ is
$$\frac{2\operatorname{ord}_\rho \zeta - \operatorname{ord}_\rho \zeta_K}{\rho(1 - \rho)},$$
and check that this agrees with the polar pair of Section 4. Show that the transform is analytic at a point where $\zeta$ and $L(s, \chi_K)$ have zeros of the same order.

*Hint.* $\operatorname{ord}_\rho \zeta_K = \operatorname{ord}_\rho \zeta + \operatorname{ord}_\rho L(s, \chi_K)$.

**Exercise 4.** Let $m \geq 1$, $q_0 = 2m$ and $d_0 = m - 1$, so that $d_0 = q_0/2 - 1$. Prove that the three hypotheses $8 \mid q_0$, $d_0 \equiv 7 \bmod 8$ and $(d_0, q_0) = 1$ of the one-sided criterion hold if and only if $8 \mid m$. Check that $m = 9240\, q$ satisfies this for every $q \geq 1$.

*Hint.* $(m - 1, 2m) = (m - 1, 2)$, since $(m - 1, m) = 1$.

**Exercise 5.** Show that the theorem on the choice of the prime in Section 5 is false for $\beta < 1/2$ and large $H$. Deduce that the hypothesis $\beta > 1/2$ of the criterion cannot be lowered by the method of this chapter, although Landau's lemma needs only $\beta > 0$.

*Hint.* By the functional equation and the reflection $L(\bar s, \bar\chi) = \overline{L(s, \chi)}$, the zeros of $L(s, \chi)$ in the strip $0 < \operatorname{Re} s < 1$ are symmetric about the line $\operatorname{Re} s = 1/2$: if $\rho$ is a zero, so is $1 - \bar\rho$. So a zero in the strip with $|\operatorname{Im} s| \leq H$ gives a zero in the box. For the existence of such zeros when $H$ is large, use the formula for the number of zeros of $L(s, \chi)$ up to height $T$ in Davenport, *Multiplicative Number Theory*, Chapter 16.

## Notes and references

The model case is classical. For Landau's theorem on Laplace transforms with a measure of one sign, the file `Lib/Analytic/Landau.lean` cites Widder, *The Laplace Transform*, Chapter II, Theorem 5b, and Montgomery and Vaughan, *Multiplicative Number Theory I*, Lemma 15.1. Montgomery and Vaughan, Chapter 15, use the theorem for one-sided bounds and oscillation theorems for $\psi(x) - x$, in the spirit of Exercise 2.

The criterion of Section 5 cites three works: Landau, "Über einen Satz von Tschebyschef", 1905; Montgomery and Vaughan, *Multiplicative Number Theory I*, Sections 15.1 and 15.2; and M. Suzuki, "On variants of Chebyshev's conjecture", arXiv 2411.07436, 2024. The theme of the 1905 paper is a claim of Chebyshev on the primes in the classes $1$ and $3$ modulo $4$. The source does not say which statements of these works it uses, and this book has not compared them with the Lean statement. The source says only that the related results in the literature need the absence of real zeros, and that its hypotheses concern only the remainders, for all primes $d$ of a class.

The zero density theorem of Section 5 cites Jutila, "On mean values of Dirichlet polynomials with real characters", Acta Arith. 27 (1975), and Heath-Brown, "A mean value estimate for real character sums", Acta Arith. 72 (1995). The source gives no theorem numbers, and its list of references marks both as works with no place given. The source proves a weak form, one good prime in each class for each box, by a mean square of theta series and the Pólya-Vinogradov inequality. It does not use Heath-Brown's large sieve for real characters. [Pólya-Vinogradov and quadratic twists](/chapter/polya-vinogradov/) in Volume 2 gives the proof. Whether the weak form follows the cited works is an open question of this book.

For the functional equation and the zeros of Dirichlet L-functions, see Davenport, *Multiplicative Number Theory*, Chapters 9 and 16. Siegel's theorem is in Chapter 21.

The source lists `Lib/Analytic/Landau` and `New/Reduction/Zeros/Criterion` among the files whose citations it has not checked. No person has checked the sign of the residues in `New.isPolar_primeRemainder` line by line against the Lean proof.

Status: drafted by a model. No person has checked this chapter against the Lean source.
