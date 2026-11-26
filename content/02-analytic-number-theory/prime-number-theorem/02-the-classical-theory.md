---
title: The classical theory
lean:
  - Lib/Analytic/PrimeNumberTheorem/ZeroFreeRegion.lean
  - New/Reduction/Zeros/PrimeNumberTheorem.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The classical theory

This section states the classical results on primes in arithmetic progressions that the chapter replaces by weaker forms. It gives each result with a source, and it says which part of each result the proof of the source uses. The proofs are in the sources. The reader who knows Davenport, *Multiplicative Number Theory*, Chapters 13 to 22, can skip to the last subsection.

### The counting functions

For $x \geq 1$, a modulus $q \geq 1$ and a class $a$ with $(a, q) = 1$, let
$$\psi(x; q, a) = \sum_{n \leq x,\ n \equiv a \bmod q} \Lambda(n), \qquad \psi(x, \chi) = \sum_{n \leq x} \chi(n)\Lambda(n).$$
The orthogonality of the characters modulo $q$ gives
$$\psi(x; q, a) = \frac{1}{\varphi(q)} \sum_{\chi \bmod q} \bar\chi(a)\, \psi(x, \chi).$$
The principal character gives the main term: $\psi(x, \chi_0) = \psi(x) + O(\log q \log x)$, and $\psi(x) \sim x$ by the prime number theorem. So the prime number theorem for the progression $a \bmod q$ is the statement $\psi(x, \chi) = o(x)$ for each $\chi \neq \chi_0$, and an error term for $\psi(x; q, a)$ is a bound for $\psi(x, \chi)$. The Dirichlet series of $\chi(n)\Lambda(n)$ is $-L'/L(s, \chi)$. So the size of $\psi(x, \chi)$ is decided by the zeros of $L(s, \chi)$ near the line $\operatorname{Re} s = 1$.

### The zero-free region

The classical argument starts from the inequality
$$3 + 4\cos\theta + \cos 2\theta = 2(1 + \cos\theta)^2 \geq 0.$$
For $\sigma > 1$ the Euler product gives $\log |L(s, \chi)| = \operatorname{Re} \sum_{p, m} \chi(p)^m p^{-ms}/m$. Apply the inequality to the angle of $\chi(p)^m p^{-imt}$ in each term. The result is
$$|L(\sigma, \chi_0)^3 L(\sigma + it, \chi)^4 L(\sigma + 2it, \chi^2)| \geq 1 \qquad (\sigma > 1). \tag{2.1}$$
This is the starting point of Hadamard and de la Vallée Poussin. A zero of $L(s, \chi)$ at $1 + it$ gives a zero of order $4$ in the middle factor as $\sigma \to 1^+$. The first factor has a pole of order $3$, and the last factor stays bounded, unless $\chi^2 = \chi_0$ and $t = 0$. So the product tends to $0$, a contradiction. To get a region, one measures how fast the product can go to $0$.

**Theorem (The classical zero-free region).** There is an absolute constant $c > 0$ with the following property. Let $\chi$ be a character modulo $q$. Then $L(s, \chi)$ has no zero in the region
$$\sigma \geq 1 - \frac{c}{\log(q(|t| + 2))},$$
except for at most one zero. If the exceptional zero exists, then $\chi$ is a real nonprincipal character, and the zero is real and simple. For each $q$ at most one real character modulo $q$ has an exceptional zero.

This is the theorem of Davenport, Chapter 14, for $L(s, \chi)$; Chapter 13 has the case $q = 1$ of $\zeta(s)$. Montgomery and Vaughan, *Multiplicative Number Theory I*, Chapter 11, prove it in the same form, and Iwaniec and Kowalski, *Analytic Number Theory*, Chapter 5, prove it for general L-functions. The classical proof does not use (2.1) directly. It uses the same inequality for $-\operatorname{Re} L'/L$, and it bounds $-\operatorname{Re} L'/L(s, \chi)$ from above by the partial fraction expansion that the Hadamard product gives. The zeros enter through the terms $\operatorname{Re} 1/(s - \rho) > 0$. The width $c/\log(q|t|)$ comes from the bound $O(\log(q|t|))$ for the number of zeros in a disc of radius $1$.

The exceptional zero $\beta_1$ is the Siegel zero. Its existence is not excluded. What is known is Siegel's theorem.

**Theorem (Siegel).** For every $\varepsilon > 0$ there is a number $C(\varepsilon) > 0$ such that $L(1, \chi) > C(\varepsilon) q^{-\varepsilon}$ for every real primitive character $\chi$ modulo $q$. Equivalently, an exceptional zero satisfies $\beta_1 < 1 - C'(\varepsilon) q^{-\varepsilon}$.

This is Davenport, Chapter 21. The constant $C(\varepsilon)$ is not effective: the proof does not give a way to compute it.

### The prime number theorem in progressions

The explicit formula for $\psi(x, \chi)$, a sum over the zeros of $L(s, \chi)$ with $|\operatorname{Im} \rho| \leq T$, with the zero-free region, gives the following.

**Theorem (Prime number theorem for progressions).** There are absolute constants $c, C > 0$ with the following property. Let $q \leq \exp(C\sqrt{\log x})$ and $(a, q) = 1$. Then
$$\psi(x; q, a) = \frac{x}{\varphi(q)} - \frac{\chi_1(a) x^{\beta_1}}{\varphi(q) \beta_1} + O\big(x \exp(-c\sqrt{\log x})\big),$$
where the second term is present only if some real character $\chi_1$ modulo $q$ has an exceptional zero $\beta_1$.

This is Davenport, Chapter 20. The explicit formula is in Chapters 17 and 19. The second term is the trace of the Siegel zero. Siegel's theorem bounds it, and gives:

**Theorem (Siegel and Walfisz).** For every $A > 0$ there is a number $c(A) > 0$ with the following property. For $q \leq (\log x)^A$ and $(a, q) = 1$,
$$\psi(x; q, a) = \frac{x}{\varphi(q)} + O_A\big(x \exp(-c(A)\sqrt{\log x})\big).$$

This is Davenport, Chapter 22. Montgomery and Vaughan, Corollary 11.19, give the theorem in this form, and the source cites that corollary for the form that it proves. The implied constants are not effective, through Siegel's theorem.

For a fixed modulus $q$ the theorem is older and simpler. There are finitely many characters, so there is a region free of zeros for all of them at once, and no question of uniformity arises. In particular the Siegel zero plays no role: for one fixed real character, a real zero $\beta < 1$ is one fixed point, and it lies to the left of the region for all large $T$. The source needs only this case.

### The Tauberian route

The explicit formula is one way from the zeros to the primes. A second way is a Tauberian theorem. Newman, *Simple analytic proof of the prime number theorem*, Amer. Math. Monthly 87 (1980), 693 to 696, proved: if $g$ is bounded and locally integrable on $[0, \infty)$, and its Laplace transform $\int_0^\infty g(v) e^{-zv}\, dv$, holomorphic in $\operatorname{Re} z > 0$, continues holomorphically to $\operatorname{Re} z \geq 0$, then $\int_0^\infty g(v)\, dv$ converges and equals the value of the transform at $0$. Zagier, *Newman's short proof of the prime number theorem*, Amer. Math. Monthly 104 (1997), 705 to 708, gives the deduction of $\psi(x) \sim x$. This route needs only $L(s, \chi) \neq 0$ on $\operatorname{Re} s = 1$, but it gives no error term. To get an error term the transform must continue to the left of the line, with bounds. Montgomery and Vaughan, Section 6.2, give a version with a contour integral; the source cites that section for its Tauberian theorem.

### What the proof needs

The proof of the source needs, for two fixed moduli $q \in \{q_0, 1\}$ and one fixed prime $d$, a bound $|R_q(y)| \leq (\log y)^{-B}$ for every $B$. Here $R_q(y)$ is the smoothed remainder
$$R_q(y) = \sum_{n \leq y} \lambda_q(n)\Big(\frac{1}{n} - \frac{1}{y}\Big) - \frac{\log y}{\varphi(q)} - c_q,$$
with $\lambda_q(n) = \Lambda(n)(1 - \chi_K(n))$ on $n \equiv 1 \bmod q$, as in [the weighted prime remainder](/chapter/weighted-prime-remainder/). This is a consequence of the Siegel and Walfisz theorem for the moduli $q$ and $qd$, by partial summation. It needs much less than that theorem:

1. The moduli are fixed. So no uniformity in $q$ is needed, and the Siegel zero does not arise.
2. The error is a power of $\log y$, not $\exp(-c\sqrt{\log y})$. In the variable $v = \log y$ it is a power of $v$, not $e^{-c\sqrt v}$. A zero-free region of width $(\log T)^{-A}$ for some fixed $A$ is enough for this. The classical width $c/\log T$ is not needed.
3. The smoothing $1/n - 1/y$ makes $R_q(e^v)$ a Lipschitz function of $v$ (Volume 1, [slow variation](/decl/New.abs_primeRemainder_exp_sub_le/)). A Lipschitz function is easy to recover from its Laplace transform, so the Tauberian step is short.

So the source proves a weak zero-free region, by a short argument from (2.1) that needs no Hadamard product, and a Tauberian theorem with a Lipschitz condition. The rest of the chapter gives these two results.

**Remark (Formalization).** The source cites Montgomery and Vaughan, Chapter 11, for its zero-free region, Lemma 10.15 for its growth bound, Section 6.2 for its Tauberian theorem, and Corollary 11.19 for the prime number theorem. Its list of references records these places as compared with the book. The source does not prove the classical theorems of this section, and it does not state them in Lean. From Mathlib the source takes (2.1) and the non-vanishing on $\operatorname{Re} s \geq 1$ (Sections 3 and 4). It takes no zero-free region to the left of the line and no prime number theorem with an error term from Mathlib: it proves the forms that it needs.
