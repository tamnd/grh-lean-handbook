---
title: Exercises and notes
lean:
  - New/Reduction/MainInequality.lean
  - New/Reduction/Lattices/Heights.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $\alpha = \sqrt[3]{2}$. Prove that $|\alpha - p/q| \geq 1/(C q^3)$ for all integers $p$ and $q \geq 1$, with an explicit constant $C$. Then write $\beta = p - q\alpha$ and check that the proof is Liouville's inequality for $\beta$ in $\mathbb{Q}(\alpha)$.

*Hint.* The integer $p^3 - 2q^3$ is not $0$. Factor it as $(p - q\alpha)(p^2 + \alpha pq + \alpha^2 q^2)$. If $|\alpha - p/q| \leq 1$, then $|p| \leq (\alpha + 1)q$, so the second factor is at most $\bigl((\alpha + 1)^2 + \alpha(\alpha + 1) + \alpha^2\bigr) q^2$. The second factor is $|N(\beta)| / |\beta|$, the product of the two complex conjugates of $\beta$.

**Exercise 2.** Let $n \geq 3$. Show that every prime $p$ with $n < p \leq 2n$ divides $\binom{2n}{n}$ exactly once, and that no prime $p$ with $2n/3 < p \leq n$ divides it. Which primes $p \leq 2n/3$ can divide it, and with which exponent at most?

*Hint.* Use the brackets $\lfloor 2n/\nu\rfloor - 2\lfloor n/\nu\rfloor \in \{0, 1\}$ of Section 3 for $\nu = p, p^2, \dots$. For $2n/3 < p \leq n$ and $n \geq 3$ one has $p^2 > 2n$. The exponent of $p$ is at most the number of $j \geq 1$ with $p^j \leq 2n$.

**Exercise 3.** In the slope inequality of Section 4, take $E = \mathbb{Z}$ with $\|1\| = 1$, $F = \mathbb{Z}^N$ with a positive definite integral Gram matrix $G$, and $\varphi(1) = v \in \mathbb{Z}^N$ with $v \neq 0$. Show that the theorem gives $v^{\mathsf T} G v \geq 1$, and give a direct proof.

*Hint.* By the example of integral lattices, $\hat\mu_{\max}(\bar F) \leq 0$. The finite part of $h(\varphi)$ is $\leq 0$, and $\|\varphi\|_\infty = (v^{\mathsf T} G v)^{1/2}$. Directly: $v^{\mathsf T} G v$ is a positive integer.

**Exercise 4.** In the proof of the main inequality (Section 5), suppose that $n = d_T$. Show that Step 4 gives $m\operatorname{rem} \leq 4L + 2I$ without the sign of the main amount. Then find where the proof uses $\mathrm{mainAmount} \geq 0$ when $n < d_T$.

*Hint.* For $n < d_T$, the inequality of Theorem C contains $(d_T - n)\,\mathrm{mainAmount}$ on the left side. A nonnegative term on the left side of an upper bound for $n\,m\operatorname{rem}$ only helps.

**Exercise 5.** Section 6 shows that $m \leq 2\sqrt x$ enters the bound $q_1 \leq x^{12}$ of [the data and its sizes](/chapter/data-and-sizes/). Suppose that $m \approx x^\theta$ with $\theta > 1/2$ and that $2^s = m^{22}$. Find the new bounds for $f$ and $q_1$ as powers of $x$. Then find one more bound of that chapter that uses the upper bound for $q_1$ or $f$.

*Hint.* The proof of $q_1 \leq x^{12}$ bounds $q_1 = q_0 \cdot 3 l_0 \cdot 2^s$, and $2^s = m^{22} \approx x^{22\theta}$. The root discriminant of $E$ is bounded by a power of $q_1$.

## Notes and references

Liouville proved his theorem on rational approximation in 1844. The product formula is in Neukirch, *Algebraic Number Theory*, Chapter III, §1. Heights of algebraic numbers are in Bombieri and Gubler, *Heights in Diophantine Geometry*, Chapter 1; the list of references of the source gives this place at second hand. Chebyshev's bound by the central binomial coefficient and Legendre's formula for $n!$ are in Hardy and Wright, *An Introduction to the Theory of Numbers*, Chapter XXII. Hardy's theorem on the zeros of $\zeta$ on the critical line is in Titchmarsh, *The Theory of the Riemann Zeta-Function*, Chapter X.

The source cites some works on bounds for sums over primes by size against divisibility: Pritsker, *The Gelfond-Schnirelman method in prime number theory* (2005); Granville and Stark, *ABC implies no Siegel zeros for L-functions of characters with negative discriminant* (2000); Bombieri, *Counting points on curves over finite fields*, Séminaire Bourbaki, exposé 430 (1973), with the place at second hand; and van Frankenhuijsen, *The Riemann hypothesis for function fields over a finite field* (2008). This book has not compared them with the source.

The slope inequality and its form with a filtration are due to Bost. The source cites Bost, *Algebraic leaves of algebraic foliations over number fields* (2001), and Gaudron, *Pentes des fibrés vectoriels adéliques sur un corps global* (2006), with no place in these works. It also cites Laurent, *Linear forms in two logarithms and interpolation determinants* (1994), for interpolation determinants: a determinant of values of functions at points is bounded above by analysis and below by the product formula. The proof of Theorem C has this shape. The source does not cite the exposé of Bost in the Séminaire Bourbaki on periods and isogenies, and this book does not use it.

The source has no model cases. The head of the compact edition (New/Main.lean of grh-compact, lines 26 to 112) gives the same plan in other names: the main amount is `mainHeight` and the unit of loss is `budget`. It says that the saving $x^{-1/2}$ is $1/m$. Sections 3, 4 and 6 of this chapter are not in the source.

[The data and its sizes](/chapter/data-and-sizes/#the-data-and-its-sizes) says that the lower bound comes from a product formula, "Theorems B and C". In the source, Theorem B gives the family of the upper bound, and only Theorem C is a lower bound (Section 5). Why $m$ has the size $\sqrt x$, and which comparison fails for a larger $m$, is open in the research notes of this book (research note b, §10, question 1).

Status: drafted by a model. No person has checked this chapter against the Lean source.
