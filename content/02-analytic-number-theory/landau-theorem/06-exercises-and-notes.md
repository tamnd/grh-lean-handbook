---
title: Exercises
lean:
  - Lib/Analytic/Landau.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $a_n \geq 0$, let $A(x) = \sum_{n \leq x} a_n$, and suppose that $A(x) \to \infty$. Prove that the abscissa of convergence of $\sum a_n n^{-s}$ is
$$\sigma_c = \limsup_{x \to \infty} \frac{\log A(x)}{\log x}.$$
Check the formula for $a_n = 1$, for $a_n = 1$ on the primes and $0$ elsewhere, and for $a_n = \Lambda(n)/\log n$ (with $a_1 = 0$).

*Hint.* If $A(x) \leq x^{\theta}$ for large $x$, partial summation gives convergence for $\sigma > \theta$. Conversely, if the series converges at $\sigma > 0$, then $A(x) \leq x^{\sigma} \sum_{n \leq x} a_n n^{-\sigma}$.

**Exercise 2.** Let $\lambda$ be the Liouville function, and let $L(x) = \sum_{n \leq x} \lambda(n)$. Prove that $\int_1^\infty L(x) x^{-s-1}\, dx = \zeta(2s)/(s\,\zeta(s))$ for $\operatorname{Re} s > 1$. Use the theorem of Section 4 on one-sided bounds, with $A(x) = L(x)/x$ and $\beta = 1/2$, to prove: if $L(x) \leq 0$ for all large $x$, then $\zeta(s) \neq 0$ for every $s$ with $\operatorname{Re} s > 1/2$. (The hypothesis is a form of Pólya's conjecture, which Haselgrove disproved in 1958. The implication is still true.)

*Hint.* $\sum \lambda(n) n^{-s} = \zeta(2s)/\zeta(s)$. In $\operatorname{Re} s > 1/2$ the function $\zeta(2s)$ is analytic and has no zeros. Check that no pole lies on $(1/2, \infty)$: use the sign of $\eta$ on $(1/2, 1)$, and the non-vanishing of $\zeta$ on $[1, \infty)$.

**Exercise 3.** Let $\chi$ be a real nonprincipal character. Show that $\zeta(\sigma)L(\sigma, \chi) \geq 1$ for every real $\sigma > 1$. Deduce directly, with no use of Landau's theorem, that $L(s, \chi)$ has no zero of order $2$ or more at $s = 1$. Explain why this direct argument does not exclude a simple zero, and what Landau's theorem adds.

*Hint.* The coefficients are $\geq 0$ and $a_1 = 1$. A double zero of $L$ at $1$ gives $\zeta(\sigma)L(\sigma, \chi) \to 0$ as $\sigma \to 1^+$. For a simple zero the product tends to a finite limit, which can be positive.

**Exercise 4.** Let $d\mu(v) = e^v (1 + v^2)^{-1}\, dv$ on $(0, \infty)$. Prove that $\sigma_c = 1$, that $F$ is bounded and continuous on the closed half-plane $\operatorname{Re} s \geq 1$, and that $F'(\sigma) \to -\infty$ as $\sigma \to 1^+$. Deduce, without Landau's theorem, that $F$ is not analytic at $1$.

*Hint.* $F'(\sigma) = -\int_0^\infty v e^{(1 - \sigma)v}(1 + v^2)^{-1}\, dv$, and $\int_0^\infty v (1 + v^2)^{-1}\, dv = \infty$. Use monotone convergence.

**Exercise 5.** Prove [Lemma](/decl/New.exists_Ioi_subset_integrableExpSet_of_analyticAt/) of Volume 1 from Landau's theorem of Section 3. That is, let $\mu$ be a measure on $\mathbb{R}$, let $X \leq 0$ be measurable, let $(a, \infty)$ lie in the interior of $S$, and let $g$ be analytic at $a$ and equal to $M$ near every real $x > a$ close to $a$. Find $b < a$ with $(b, \infty) \subset S$.

*Hint.* Let $\nu$ be the image of $\mu$ under $-X$, a measure on $[0, \infty)$, so that $\int e^{tX}\, d\mu = \int e^{-tu}\, d\nu(u)$. Let $\sigma_c$ be the abscissa of $\nu$. If $\sigma_c < a$, any $b$ between them works. If $\sigma_c = a$, use the identity theorem on $D \cap \{\operatorname{Re} s > a\}$, for a disc $D$ about $a$ on which $g$ is analytic, and apply the theorem.

**Exercise 6.** In the Lean proof of `New.exists_mul_exp_le`, find the one step that uses the hypothesis `hβ : 0 < β`, and check that the constant of the remark in Section 5 removes it. Then find, in the proof of `New.IsPolar.landau`, the step that uses `hβ` for the residues of the polar function, and explain why that use cannot be removed with the definition `New.IsPolar` as it is.

*Hint.* The first use is the inequality $1 \leq e^{\beta v}$ for $v > 0$. The second is the call of property (c) of the polar function at a point $\rho$ with $\beta < \operatorname{Re} \rho$, which needs $0 < \operatorname{Re} \rho$.

## Notes and references

Landau proved the theorem in 1905, in "Über einen Satz von Tschebyschef", to study a claim of Chebyshev on the primes in the classes $1$ and $3$ modulo $4$. The form for Dirichlet series with nonnegative coefficients is Montgomery and Vaughan, *Multiplicative Number Theory I* (2007), Theorem 1.7, and the form for Mellin integrals of functions of one sign is Lemma 15.1 of the same book. Montgomery and Vaughan, Chapter 15, apply the theorem to the oscillation of error terms in prime number theory, as in Section 4, and give the sharper results of Littlewood. The analogue for power series is Pringsheim's theorem. For Laplace-Stieltjes transforms, `Lib/Analytic/Landau.lean` cites Widder, *The Laplace Transform* (1941), Chapter II, Theorem 5b. This book has not compared that statement with the Lean statement. Davenport, *Multiplicative Number Theory*, Chapter 4, proves $L(1, \chi) \neq 0$, and Chapter 15 counts the zeros of $\zeta$.

This treatment differs from the textbooks in three points. First, it proves the local theorem with the full radius of analyticity, from which the classical forms are corollaries. Volume 1 proves the theorem with a loss of a constant factor in the radius, and the source with a loss of a factor $2$ or more, since the argument needs only some convergence to the left. Second, it states the continuation along the real axis with meromorphic functions, because the applications know a continuation with poles. Third, it compares the classical theorem with the form of the source, which is stated for moment generating functions of Mathlib and which allows real poles with residues of the right sign.

The source cites Montgomery and Vaughan, Lemma 15.1, in the module docstring of `Lib/Analytic/Landau.lean`. The list of references of the source puts `Lib/Analytic/Landau` among the files whose citations were not checked against their sources (finding F-101). No person has checked the Lean proofs of this chapter line by line against the text.

Status: drafted by a model. No person has checked this chapter against the Lean source.
