---
title: Exercises
lean:
  - Lib/Analytic/PrimeNumberTheorem/ZeroFreeRegion.lean
  - Lib/Analytic/PrimeNumberTheorem/Tauberian.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $\chi$ be the nonprincipal character modulo $4$. Show that $L(1, \chi) = \pi/4$. Find an explicit $C$ with $|L'(z, \chi)| \leq C$ for $|z - 1| \leq 1/2$. Deduce that the hypothesis of [the uniform form](/decl/New.norm_logDeriv_entireL_le/) for real characters, $|f_\chi(z)| \geq 1/l$ for $|z - 1| \leq 1/l$, holds for every $l \geq 10^{10}$. So for this $\chi$ the threshold of [the zero-free region](/decl/New.eventually_norm_logDeriv_entireL_le/) can be $10^{10}$.

*Hint.* $L(1, \chi) = 1 - 1/3 + 1/5 - \cdots$ is the series of $\arctan 1$. For $L'$, use partial summation with $|\sum_{n \leq t} \chi(n)| \leq 1$, as in Section 3. Then $|f_\chi(z) - \pi/4| \leq C/l$.

**Exercise 2.** In Section 4 replace the step length $2l^{-25}$ by $2l^{-a}$ and the width $l^{-25}$ by $l^{-a}$, for a real $a > 0$. Show that the 3-4-1 bound gives $|f_\chi(v)| \geq \tfrac14 l^{-(3a + 7)/4}$ at $v = s + 2l^{-a}$, and that the step changes $f_\chi$ by at most $4l^{3 - a}$. Deduce that the argument proves a zero-free region of width $l^{-a}$ for large $l$ if $a > 19$, and that it fails for $a \leq 19$. Which value of $a$ does the source use, and how much room does it leave?

*Hint.* $256^{1/4} = 4$. Compare the exponents: $3 - a < -(3a + 7)/4$ if and only if $a > 19$. The source uses $a = 25$, where the lower bound is $\tfrac14 l^{-20.5}$, and it replaces it by the weaker $12l^{-22}$ to keep integer exponents.

**Exercise 3.** Let $R(v) = v$ and $R(v) = v^2$ on $[0, \infty)$. Compute $\Phi(s) = \int_0^\infty R(v) e^{(1 - s)v}\, dv$, and compute the coefficient $(-H)^k H\, \Phi^{(k)}(1 + H)/k!$ with $H = (k + 1)/u$. Show that it is $u$ for $R(v) = v$ and $u^2(1 + 1/(k + 1))$ for $R(v) = v^2$. Explain the second answer with the mean and the variance of the Gamma density in (5.1).

*Hint.* $\Phi(s) = (s - 1)^{-2}$ and $2(s - 1)^{-3}$. Or use [the Gamma integrals](/decl/New.integrableOn_and_integral_pow_mul_exp_neg_mul/) with $j = k + 1$ and $j = k + 2$.

**Exercise 4.** Suppose that $F$ in the Tauberian theorem satisfies the hypothesis with the classical width: for large $l$, $F$ is holomorphic and at most $l^A$ on $\operatorname{Re} s \geq 1 - c/l$, $|s| \leq e^l$. Show that the proof of Section 5 gives $|R(u)| \leq \exp(-c'\sqrt u)$ for large $u$, with some $c' > 0$ that depends on $c$.

*Hint.* Take $\delta = e^{-\alpha\sqrt u}$, $k + 1 \approx u^2/\delta^2$, $H = (k + 1)/u$ and $l = \beta\sqrt u$ with $\beta > 2\alpha$, so that the disc lies in $|s| \leq e^l$. The Lipschitz error is about $2L\delta$. [The coefficient is small](/decl/New.norm_taylorCoeff_dslope_le/) with $\eta = c/l$ gives a bound $e^{2\alpha\sqrt u}$ times a power of $u$ times $\exp(-c\sqrt u/(2\beta))$. Choose $\alpha$ small and $\beta = 3\alpha$, so that $c > 12\alpha^2$.

**Exercise 5.** Let $\chi$ be a character modulo $q$ with $\chi^2 \neq \chi_0$. Show from the Lean statements that [the zero-free region](/decl/New.eventually_norm_logDeriv_entireL_le/) holds for every $l \geq \max(10^{10}, q)$. Then let $\chi$ be real and nonprincipal. Explain where the 3-4-1 bound of Section 4 fails for $s$ near $1$, and why the source cannot remove the hypothesis on $f_\chi$ near $1$ by a better estimate of the same kind.

*Hint.* For $\chi^2 \neq \chi_0$ the hypothesis `h_near` of `New.norm_logDeriv_entireL_le` has a false premise. For a real $\chi$ the point $s_2 = \sigma + 2it$ is near the pole of $L(s, \chi^2) = L(s, \chi_0)$ when $s$ is near $1$. A real zero $\beta$ near $1$ makes $|f_\chi|$ small near $1$, and (2.1) says nothing against it. To exclude such a zero in terms of $q$ is the problem of the Siegel zero.

**Exercise 6.** In Lean, `logDeriv f s` is `deriv f s / f s`, and $x/0 = 0$. Show that at a zero $s$ of $\tilde L(\cdot, \chi)$ the value `logDeriv (entireL χ) s` is $0$. Deduce that the second half of the conclusion of [the zero-free region](/decl/New.eventually_norm_logDeriv_entireL_le/), the bound $2l^{25}$, does not imply the first half, $\tilde L(s, \chi) \neq 0$. Where does Volume 1 use the first half?

*Hint.* Look at the proof of `New.eventually_norm_logDerivMean_div_le`. The first half gives that the function $G_q$ is holomorphic on the region, by `New.analyticAt_logDerivMean`. The bound alone would allow junk values at the zeros.

## Notes and references

The zero-free region of de la Vallée Poussin for $\zeta$ and for $L(s, \chi)$, with the exceptional zero, is in Davenport, *Multiplicative Number Theory*, Chapters 13 and 14, and in Montgomery and Vaughan, *Multiplicative Number Theory I*, Chapter 11. Iwaniec and Kowalski, *Analytic Number Theory*, Chapter 5, treat zero-free regions for general L-functions. Siegel's theorem is Davenport, Chapter 21. The prime number theorem for progressions is Davenport, Chapter 20, from the explicit formula of Chapters 17 and 19, and the theorem of Siegel and Walfisz is Davenport, Chapter 22, and Montgomery and Vaughan, Corollary 11.19.

The argument of Section 4 bounds $|L|$ and $|L'|$ and uses (2.1) with absolute values. It needs no Hadamard product, and it gives a region of width a negative power of $\log T$ only. The source gives the argument for all Dirichlet characters at once, with explicit constants and a uniform dependence on the modulus.

The Tauberian route to the prime number theorem is due to Newman, Amer. Math. Monthly 87 (1980), 693 to 696, in the form of Zagier, Amer. Math. Monthly 104 (1997), 705 to 708. Montgomery and Vaughan, Section 6.2, give a Tauberian theorem with a contour integral. The source cites that section. Its method, the Taylor coefficient at a far point read in two ways, is the inversion formula of Post and Widder for the Laplace transform, with the Cauchy estimate in place of a limit.

The source cites Montgomery and Vaughan, Chapter 11, Lemma 10.15, Section 6.2 and Corollary 11.19 in the files of this chapter. Its list of references records these places as compared with the book. This book has not compared them.

Status: drafted by a model. No person has checked this chapter against the Lean source.
