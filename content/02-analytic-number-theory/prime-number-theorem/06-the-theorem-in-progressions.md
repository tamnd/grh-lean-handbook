---
title: The theorem in progressions
lean:
  - Lib/Analytic/PrimeNumberTheorem/ZeroFreeRegion.lean
  - Lib/Analytic/PrimeNumberTheorem/Tauberian.lean
  - New/Reduction/Zeros/PrimeNumberTheorem.lean
  - Lib/Analytic/Primes.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The theorem in progressions

This section puts the zero-free region of Section 4 and the Tauberian theorem of Section 5 together. It shows how Volume 1 gets the prime number theorem for the weighted remainder $R_q$, and how Chapter 5 uses the uniform form of the region. Then it lists exactly what the source proves and what it takes from Mathlib, and it compares the result with the classical theorems of Section 2. The statements of the source for $R_q$ are in Volume 1, [the prime number theorem at the cut-off](/chapter/main-inequality/#the-prime-number-theorem-at-the-cut-off). This section does not restate them; it explains the analytic part of their proofs.

### The function F of the prime remainder

Fix an odd prime $d$ and a modulus $q \geq 1$ prime to $d$. Let $\chi_K(n) = (n/d)$ be the Legendre symbol, and let
$$\lambda_q(n) = \Lambda(n)\big(1 - \chi_K(n)\big) \quad \text{if } n \equiv 1 \bmod q, \qquad \lambda_q(n) = 0 \text{ otherwise}.$$
For a character $\psi$ modulo $q$, let $\psi'$ be the character $n \mapsto \psi(n)\chi_K(n)$ modulo $qd$. The source calls it `quadTwist ψ d`. Orthogonality of the characters modulo $q$ gives, for $\operatorname{Re} s > 1$,
$$\sum_{n \equiv 1 \bmod q} \frac{\Lambda(n)(1 - \chi_K(n))}{n^s} = \frac{1}{\varphi(q)} \sum_{\psi \bmod q} \Big(-\frac{L'}{L}(s, \psi) + \frac{L'}{L}(s, \psi')\Big).$$
The principal character modulo $q$ contributes the pole $1/(s - 1)$, from $-\zeta'/\zeta$. The source removes it with $\tilde L$. Its function is
$$G_q(s) = \frac{1}{\varphi(q)}\Big(\sum_{\psi \bmod q}\Big(\frac{\tilde L'}{\tilde L}(s, \psi') - \frac{\tilde L'}{\tilde L}(s, \psi)\Big) - 1\Big),$$
which is `New.logDerivMean`. For $\operatorname{Re} s > 1$ it equals $\sum_n \lambda_q(n) n^{-s} - s/(\varphi(q)(s - 1))$. The constant of the remainder is $c_q = \operatorname{Re} G_q(1)$, and
$$R_q(y) = \sum_{n \leq y} \lambda_q(n)\Big(\frac{1}{n} - \frac{1}{y}\Big) - \frac{\log y}{\varphi(q)} - c_q$$
is `New.primeRemainder` (Volume 1, [the weighted prime remainder](/chapter/weighted-prime-remainder/)). Partial summation, in Volume 1, gives the transform: for $\operatorname{Re} s > 2$,
$$\frac{F(s) - F(1)}{s - 1} = \int_0^\infty R_q(e^v)\, e^{(1 - s)v}\, dv, \qquad F(s) = \frac{G_q(s)}{s}.$$
This is the hypothesis on the transform in [the Tauberian theorem](/decl/New.eventually_abs_le_inv_pow_of_transform/), with $R(v) = R_q(e^v)$.

### The bound for F

The region hypothesis of the Tauberian theorem asks: for all large $l$, $F$ is holomorphic and at most $l^A$ on $\operatorname{Re} s \geq 1 - l^{-A}$, $|s| \leq e^l$. Volume 1 proves it with $A = 26$, in [the bound for the mean of logarithmic derivatives](/decl/New.eventually_norm_logDerivMean_div_le/). The proof is short, and it shows where the exponent $26$ comes from.

There are finitely many characters $\psi$ modulo $q$, and finitely many twists $\psi'$ modulo $qd$. Apply [the zero-free region](/decl/New.eventually_norm_logDeriv_entireL_le/) to each of them. A finite intersection of events "for all large $l$" is again such an event. So for all large $l$, every $\tilde L(s, \psi)$ and every $\tilde L(s, \psi')$ is nonzero on $\operatorname{Re} s \geq 1 - l^{-25}$, $|s| \leq e^l$, with logarithmic derivative at most $2l^{25}$. Let $N$ be the number of characters modulo $q$. Then on that region
$$|G_q(s)| \leq N \cdot 2 \cdot 2l^{25} + 1.$$
Take $l \geq 8N + 2$. The region $\operatorname{Re} s \geq 1 - l^{-26}$ lies in $\operatorname{Re} s \geq 1 - l^{-25}$ and in $\operatorname{Re} s \geq 1/2$, so $|s| \geq 1/2$ and
$$|F(s)| \leq 2(4Nl^{25} + 1) \leq (8N + 2) l^{25} \leq l^{26}.$$
So the larger exponent $26$ absorbs the constant $8N + 2$. $G_q$ is holomorphic there because no $\tilde L$ in it vanishes.

The Lipschitz hypothesis is [slow variation](/decl/New.abs_primeRemainder_exp_sub_le/) of Volume 1: $|R_q(e^v) - R_q(e^u)| \leq 26(v - u)$ for $0 \leq u \leq v \leq u + 1$. So $L = 26$. That the two constants are both $26$ is a coincidence of the bounds.

The Tauberian theorem gives, for every natural number $B$, $|R_q(e^v)| \leq v^{-B}$ for all large $v$. With $y = e^v$ this is
$$|R_q(y)| \leq (\log y)^{-B} \qquad \text{for all large } y,$$
which is [the prime number theorem for $R_q$](/decl/New.eventually_abs_primeRemainder_le/). With $B = 1$ it gives [$R_q(y) \to 0$](/decl/New.tendsto_primeRemainder/). So $c_q$ is the right constant: it is the limit of $\sum_{n \leq y} \lambda_q(n)(1/n - 1/y) - \log y/\varphi(q)$.

**Remark (Formalization).** The source defines $G_q$ with `logDeriv`, which is $f'/f$ with the convention $x/0 = 0$ of Lean. So $G_q(s)$ has a value also at a zero of some $\tilde L$, and $c_q = \operatorname{Re} G_q(1)$ is defined with no hypothesis. At $s = 1$ no $\tilde L$ vanishes (Section 4, [no small values near 1](/decl/New.eventually_le_norm_regularL/), from Mathlib), so $G_q(1)$ is the true value of the meromorphic function. In the region of the bound no $\tilde L$ vanishes, so the junk value plays no role there. The theorem $R_q(y) \to 0$ shows that the definition of $c_q$ by a value at $1$ agrees with the classical definition as a limit.

### The uniform use: primes in windows

Chapter 5 needs a prime $p \equiv 1 \bmod M^k$ with $\log p$ in a window, uniformly in $k$. There the modulus $M^k$ is not fixed, and [the zero-free region](/decl/New.eventually_norm_logDeriv_entireL_le/) for one character does not suffice: its threshold $l_0$ depends on the character. The source uses [the uniform form](/decl/New.norm_logDeriv_entireL_le/) instead, in the lemma `New.eventually_norm_logDeriv_entireL_le_near_one` of `Lib/Analytic/Primes.lean`. Its statement is: let $A$ be a natural number and $4 \mid M$. For all large $X$, for every $k > 1$, every character $\chi$ modulo $M^k$ and every $s$ with $M^k \leq X^A$ and $|s - 1| \leq X^{-1}$,
$$\tilde L(s, \chi) \neq 0 \qquad \text{and} \qquad \Big|\frac{\tilde L'}{\tilde L}(s, \chi)\Big| \leq X.$$
The proof takes $l = (A + 1)\log X$, so that $e^l = X^{A + 1} \geq M^k$. For large $X$, $X^{-1} \leq l^{-25}$, so the disc $|s - 1| \leq X^{-1}$ lies in the region of the uniform form, and $2l^{25} \leq X$. The only hypothesis left is the lower bound near $1$ for real characters. A character $\chi$ modulo $M^k$ with $\chi^2 = \chi_0$ comes from a character modulo $M^2$, when $4 \mid M$. There are finitely many characters modulo $M^2$, and the source applies [no small values near 1](/decl/New.eventually_le_norm_regularL/) to each of them. This gives one threshold for all $k$. Chapter 5, [primes in windows](/chapter/primes-in-windows/), gives the rest of the argument, and Volume 1, [the data exist](/chapter/data-exist/), uses the prime.

This use needs only a disc of radius $X^{-1}$ about $1$, with $\log M^k \leq A\log X$. In the classical language: no zero of $L(s, \chi)$ in $|s - 1| \leq (\log q)^{-c}$ for a constant $c$, for $q = M^k$, with the real characters coming from one fixed modulus. A Siegel zero of a character modulo $M^k$ would be a zero of a character modulo $M^2$, which is a fixed finite set of L-functions. So the Siegel zero does not arise here either.

### What the source proves and what it takes

The source proves every result of Sections 3 to 5 in `Lib/Analytic/PrimeNumberTheorem`, and the application in `New/Reduction/Zeros/PrimeNumberTheorem.lean`. It takes the following from Mathlib.

1. The 3-4-1 inequality for Dirichlet series, `DirichletCharacter.norm_LSeries_product_ge_one`.
2. The non-vanishing $L(s, \chi) \neq 0$ for $\operatorname{Re} s \geq 1$, `DirichletCharacter.LFunction_ne_zero_of_one_le_re`, through [the lemma on $\tilde L$](/decl/New.entireL_ne_zero/) of Chapter 1. For a real nonprincipal $\chi$ this contains Dirichlet's theorem $L(1, \chi) \neq 0$.
3. The identity of the L-function with its Dirichlet series for $\operatorname{Re} s > 1$, and its analytic continuation, as in Chapter 1.
4. Partial summation for a Dirichlet series, `LSeries_eq_mul_integral'`, and the bounds for $\zeta(\sigma)$ near $1$ from `ZetaAsymptotics` (Section 3).
5. The three lines theorem of Hadamard and the Cauchy estimates (Section 3 and Section 5).
6. The Laplace transform of $v^j$, and differentiation under the integral sign (Section 5).

It takes from Mathlib no zero-free region to the left of $\operatorname{Re} s = 1$, no prime number theorem, no explicit formula, and no Hadamard product. It does not use the functional equation of $L(s, \chi)$.

### Comparison with the classical theorems

The classical theorem of Section 2 for a fixed modulus gives $\psi(x; q, a) = x/\varphi(q) + O(x\exp(-c\sqrt{\log x}))$. The source proves a weaker statement in three ways.

1. *The sum.* It treats one weighted sum, over $n \equiv 1 \bmod q$ with the weight $1 - \chi_K(n)$ and the smoothing $1/n - 1/y$. This is a sum of the logarithmic type $\sum \Lambda(n)/n$, not $\psi$. The sum $\psi(x; q, 1)$ does not appear.
2. *The error.* The error $(\log y)^{-B}$ for every $B$ is weaker than $\exp(-c\sqrt{\log y})$. For the logarithmic sum the classical theorem would give an error $O(\exp(-c\sqrt{\log y}))$.
3. *The uniformity.* The theorem is for one fixed $q$ and $d$. Nothing is said about how large $y$ must be in terms of $q$.

The theorem of Siegel and Walfisz gives the classical error uniformly in $q \leq (\log x)^A$. The source cites Montgomery and Vaughan, Corollary 11.19, and calls its result a consequence of that theorem. That is correct in substance: partial summation from the Siegel and Walfisz theorem for the moduli $q$ and $qd$ gives the bound for $R_q$. The source does not use this route. It proves its weak form directly.

**Remark (Formalization).** The source gives no explicit $y_0$ for which $|R_q(y)| \leq (\log y)^{-B}$ holds for $y \geq y_0$. It states the theorem with a filter, "for all large $y$". The threshold depends on the threshold $l_0$ of the zero-free region, which depends on $r_0$ for the real characters, which comes from continuity at $s = 1$. In principle a lower bound for $|L(1, \chi)|$ and an upper bound for $|L'|$ near $1$ would make $r_0$ explicit for each fixed real $\chi$, so the result is effective for each fixed $q$ in the classical sense. The source does not do this, and it does not need to: Volume 1 needs only the existence of a threshold for two fixed moduli. The ineffective constant of Siegel's theorem does not enter.

**Remark (Formalization).** The chapter does not use [Landau's theorem](/chapter/landau-theorem/), [the polar functions](/chapter/polar-functions/) or the zeros of any L-function to the left of the region. In particular, the proof of the source does not assume any zero-free region or zero density estimate. It proves the one region that it uses. The plan of the source, [the theorem and the plan](/chapter/theorem-and-plan/), needs this: an argument that assumed a zero-free region for the L-functions that it studies would be circular.

**Remark (Formalization).** All constants are explicit except the thresholds given by filters. The exponents $25$ and $26$, the constants $10^{10}$, $256$, $12$, $8$ and $4$ of Section 4, and the choices $k = \lfloor u^{2B + 4} \rfloor$, $l = (2B + 5)\log u$ of Section 5 are in the Lean statements or proofs, and the book keeps them. None of them is optimal. Exercise 2 finds the least exponent for the step of Section 4.
