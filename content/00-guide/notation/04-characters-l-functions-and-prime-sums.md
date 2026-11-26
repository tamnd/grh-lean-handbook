---
title: Characters, L-functions and prime sums
lean:
  - Lib/General/NumberTheory/ImaginaryQuadraticField.lean
  - New/Reduction/Zeros/PrimeError.lean
  - New/Reduction/Data/AdmissibleData.lean
  - New/Reduction/PrimeSums.lean
decls:
  - New.quadTwist
  - New.entireL
  - New.lambdaKResidueClass
  - New.lambdaKSum
  - New.logDerivMean
  - New.primeRemainder
  - New.re_logDerivMean_one
  - New.primeRemainder_eq_sum_posPart
  - New.Data.primeSum
  - New.Data.jetSize
  - New.Data.directionAmount
  - New.Data.mainAmount
  - New.Data.mainPrimeSum
  - New.Data.totalRemainder
  - New.Data.totalRemainder_eq
  - New.Data.errorUnit
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Characters, L-functions and prime sums

This section fixes the letters for Dirichlet characters, their $L$-functions, the weights of the prime sums, the remainders, and the amounts that the main inequality compares. The characters and $L$-functions are those of Mathlib. Volume 1, [the half-plane and the line](/chapter/half-plane-to-line/), states their classical properties, and [the weighted prime remainder](/chapter/weighted-prime-remainder/) and [the prime sums](/chapter/prime-sums/) use them.

### Dirichlet characters

A Dirichlet character modulo $q$ is a multiplicative character of $\mathbb{Z}/q\mathbb{Z}$, with the value $0$ at the classes that are not units. Mathlib's type is `DirichletCharacter R q`, with values in a commutative ring $R$. The book takes $R = \mathbb{C}$ unless it says otherwise; the character $\chi_K$ of Section 2 has values in $\mathbb{Z}$.

The letters are as follows. The letter $\chi$ is a general character, and $\psi$ is a character modulo $q$ in a sum over all characters modulo $q$. The principal character modulo $q$ is written $1$ or $\chi_0$, as in Mathlib. The inverse of $\chi$ is its complex conjugate $\bar\chi$; Mathlib writes `χ⁻¹`. A character modulo $q$ is also a character modulo every multiple of $q$, by Mathlib's `DirichletCharacter.changeLevel`. The book says "the character modulo $q'$ induced by $\chi$" for this, and it writes $\chi$ for both when the modulus is clear.

**Definition (The twist by $\chi_K$).** For a character $\psi$ modulo $N$, the twist $\psi\chi_K$ is the product of $\psi$ and $\chi_K$, both read as characters modulo $N d$.

Lean: `New.quadTwist` (Lib/General/NumberTheory/ImaginaryQuadraticField.lean).

Lean writes `quadTwist ψ d`. For $N = 1$ and $\psi = 1$ the twist is $\chi_K$ itself, as a character modulo $1 \cdot d$. The constant $C_d$ of Section 2 is written with this form of $\chi_K$.

### The L-functions

Mathlib's `DirichletCharacter.LFunction` is the function $L(s, \chi)$, equal to $\sum_{n \geq 1} \chi(n) n^{-s}$ for $\operatorname{Re} s > 1$ and continued to $\mathbb{C}$. It is the $L$-function at the modulus of $\chi$, not at its conductor: if $\chi$ is induced from a character $\chi^*$, then $L(s, \chi) = L(s, \chi^*) \prod_{p \mid q}(1 - \chi^*(p) p^{-s})$. For the principal character it has a pole at $s = 1$, and Mathlib gives it the value of the continuation formula there.

**Definition (The entire L-function $\tilde L$).** For a character $\chi$ modulo $N \geq 1$, $\tilde L(s, \chi) = L(s, \chi)$ if $\chi$ is not principal. If $\chi$ is principal, $\tilde L(s, \chi)$ is the entire function equal to $(s - 1) L(s, \chi)$ for $s \neq 1$.

Lean: `New.entireL` (Lib/General/NumberTheory/ImaginaryQuadraticField.lean), with `DirichletCharacter.LFunction` (Mathlib) and `DirichletCharacter.LFunctionTrivChar₁` (Mathlib).

The book writes $\tilde L$, and so does Volume 1. The comments of the source write $E_\chi$ for it. The book does not use $E_\chi$, because $E$ is the field. For $N = 1$ one has $\tilde L(s, 1) = (s - 1)\zeta(s)$.

The completed $L$-function of Mathlib, `DirichletCharacter.completedLFunction`, is written $\Lambda(s, \chi)$. It is $L(s, \chi)$ times the gamma factor $\Gamma_{\mathbb{R}}(s + \mathfrak{a})$, with $\Gamma_{\mathbb{R}}(s) = \pi^{-s/2}\Gamma(s/2)$ (Mathlib's `Complex.Gammaℝ`) and $\mathfrak{a} \in \{0, 1\}$ the parity, and it has no factor $q^{s/2}$. The letter $\Lambda$ also names the von Mangoldt function $\Lambda(n)$. The book keeps both, as Iwaniec and Kowalski do, since the completed function has two arguments $(s, \chi)$ and the von Mangoldt function has one integer argument. In Volume 1, [the half-plane and the line](/chapter/half-plane-to-line/) gives the parity the letter $a(\chi)$; the book writes $\mathfrak{a}$ in this place, since $a$ is the long order.

### The weights of the prime sums

**Definition (The weights $\lambda_q$ and $\Lambda_K$).** For $q \geq 1$ and $n \geq 1$,
$$\lambda_q(n) = \begin{cases} \Lambda(n)\,(1 - \chi_K(n)) & \text{if } n \equiv 1 \bmod q, \\ 0 & \text{otherwise,} \end{cases} \qquad \Lambda_K = \lambda_1.$$

Lean: `New.lambdaKResidueClass` (New/Reduction/Zeros/PrimeError.lean), with `ArithmeticFunction.vonMangoldt.residueClass` (Mathlib) for the restriction to $n \equiv 1 \bmod q$.

Lean writes `lambdaKResidueClass d q n`. For a prime power $n = p^e$, the factor $1 - \chi_K(p^e)$ is $0$ if $p$ splits in $K$, $1$ if $p = d$, and $1 - (-1)^e$ if $p$ is inert. So $\Lambda_K(n) \in \{0, \log p, 2\log p\}$, and it is $2 \log p$ at the inert primes. Volume 1 writes $\lambda$ for $\lambda_q$ when $q$ is fixed, and the book does the same in a proof where $q$ does not change.

**Definition (The partial sums).** For $r \in \{0, 1\}$ and $y > 0$, $S_r(y) = y^{-r} \sum_{1 \leq n \leq y} \lambda_q(n)\, n^{r-1}$. So $S_0(y) = \sum_{n \leq y} \lambda_q(n)/n$ and $S_1(y) = y^{-1}\sum_{n \leq y} \lambda_q(n)$.

Lean: `New.lambdaKSum` (New/Reduction/Zeros/PrimeError.lean).

The letters $S_0$ and $S_1$ are local. The letter $r$ here is not the rank $r$ of the data.

**Definition (The function $G_q$ and the constant $c_q$).** For $q \geq 1$,
$$G_q(s) = \frac{1}{\varphi(q)}\Bigl(\sum_{\psi \bmod q}\Bigl(\frac{\tilde L'}{\tilde L}(s, \psi\chi_K) - \frac{\tilde L'}{\tilde L}(s, \psi)\Bigr) - 1\Bigr), \qquad c_q = \operatorname{Re} G_q(1).$$

Lean: `New.logDerivMean` (New/Reduction/Zeros/PrimeError.lean).

Lean writes `logDerivMean d q s`, with Mathlib's `logDeriv f = f'/f`. The function $G_q$ has a value at every $s$, as `logDeriv` does. Volume 1 proves that $G_q$ is analytic on $\operatorname{Re} s \geq 1$, so $c_q$ is the value of an analytic function. For odd $d$ prime to $q$ and $\operatorname{Re} s > 1$, $\sum_n \lambda_q(n) n^{-s} = s/(\varphi(q)(s-1)) + G_q(s)$.

**Lemma.** For a prime $d$, $c_1 = -1 - C_d$.

Lean: `New.re_logDerivMean_one` (New/Reduction/Zeros/PrimeError.lean).

*Proof.* There is one character modulo $1$, and $\varphi(1) = 1$. So $G_1(s) = \tilde L'/\tilde L(s, \chi_K) - Z'/Z(s) - 1$ with $Z(s) = (s - 1)\zeta(s)$. Since $(s - 1)\zeta(s) = 1 + \gamma(s - 1) + O((s-1)^2)$ near $s = 1$, one has $Z'/Z(1) = \gamma$. So $\operatorname{Re} G_1(1) = \operatorname{Re} \tilde L'/\tilde L(1, \chi_K) - \gamma - 1 = -C_d - 1$. $\square$

The book writes $C_d$, and so does Volume 1.

**Definition (The remainder $R_q$).** For $q \geq 1$ and real $y$,
$$R_q(y) = \sum_{n \leq y} \lambda_q(n)\Bigl(\frac1n - \frac1y\Bigr) - \frac{\log y}{\varphi(q)} - c_q.$$

Lean: `New.primeRemainder` (New/Reduction/Zeros/PrimeError.lean).

Lean defines `primeRemainder d q y` as $S_0(y) - S_1(y) - \log y/\varphi(q) - c_q$, which is the formula above for $y > 0$. For $y > 0$ and every integer $A \geq \lfloor y \rfloor$, the sum is also $\sum_{n \leq A} \lambda_q(n)(1/n - 1/y)_+$, by `New.primeRemainder_eq_sum_posPart`. The letter $R_q$ always has its subscript, and it always depends on $d$; the book writes $R_q^{(d)}$ only where two primes $d$ occur.

### The prime sums and the amounts

**Definition (The prime sum $s_{\mathrm{fin}}$).** For real $y$ and a place $\sigma$,
$$s_{\mathrm{fin}}(y, \sigma) = \sum_{1 \leq \nu \leq a} \Lambda_K(\nu)\,\bigl(y/\nu - \kappa([-\nu]\sigma)\bigr)_+.$$

Lean: `New.Data.primeSum` (New/Reduction/Data/AdmissibleData.lean).

Here $[-\nu]\sigma$ is the product in $\Phi$ of the place $[-\nu]$ of Section 2 and $\sigma$. The sum has the upper limit $a$ for every $y$; for $y \leq a$ the terms with $\nu > y$ are $0$, since $\kappa \geq 0$.

**Definition (The jet size $s_\infty$).** For $j \in \mathbb{N}$, $s_\infty(j) = \log j! + j \log(M/\Omega)$.

Lean: `New.Data.jetSize` (New/Reduction/Data/AdmissibleData.lean).

**Definition (The direction amount and the main amount).**
$$\mathrm{dir} = \sum_{\sigma \in \Phi}\bigl(s_\infty(\kappa(\sigma)) - s_{\mathrm{fin}}(\kappa(\sigma), \sigma)\bigr), \qquad \mathrm{main} = m\, k\, \mathrm{dir}.$$

Lean: `New.Data.directionAmount` (New/Reduction/Data/AdmissibleData.lean), `New.Data.mainAmount` (New/Reduction/PrimeSums.lean).

The book writes $\mathrm{main}$ for the main amount, and so does Volume 1. In the book $M$ is always the principal level $p_0 p_1$, never the main amount.

**Definition (The expected value and the total remainder).**
$$s_{\mathrm{main}} = a\Bigl(\log a - \frac1f \sum_{\tau \in \Phi} \log\kappa(\tau) + c_1\Bigr), \qquad \mathrm{rem} = \sum_{\tau \in \Phi_a}\bigl(s_{\mathrm{fin}}(a, \tau) - s_{\mathrm{main}}\bigr).$$

Lean: `New.Data.mainPrimeSum` (New/Reduction/PrimeSums.lean), `New.Data.totalRemainder` (New/Reduction/PrimeSums.lean).

So $s_{\mathrm{main}} = a(\log(a/\bar\kappa) + c_1)$, with $\bar\kappa$ the geometric mean of the weights.

**Lemma.** $\mathrm{rem} = a\bigl(\#\Phi_b\,(R_{q_0}(x) - R_{q_0}(x_1)) + \#\Phi_a\, R_1(x_1)\bigr)$.

Lean: `New.Data.totalRemainder_eq` (New/Reduction/PrimeSums.lean).

Volume 1, [the prime sums](/chapter/prime-sums/), proves this lemma. It is the place where the remainders $R_{q_0}$ and $R_1$, with the prime $d$ of the parameters, enter the main inequality.

**Definition (The unit of loss).** $\mathrm{err}_0 = f\, a \log^3 b$.

Lean: `New.Data.errorUnit` (New/Reduction/Data/AdmissibleData.lean).

The book writes $\mathrm{err}_0$ for this unit. The word $\mathrm{err}$ also names two other objects: the divisibility errors `New.Data.divisibilityError` and the total error $4 f a \log^4 b + 2I$ of the main inequality. The book keeps $\mathrm{err}(p)$, with its argument, for the divisibility errors, and writes $\mathrm{err}$ with no argument for the total error.

**Example.** Let $\sigma \in \Phi_b$ and $y = \kappa(\sigma) = b$. The term $\nu = 1$ of $s_{\mathrm{fin}}(b, \sigma)$ has $\Lambda_K(1) = 0$. A term $\nu = p$, an inert prime with $p \nmid q_1$, has the weight $2 \log p$ and the factor $(b/p - \kappa([-p]\sigma))_+$. The place $[-p]\sigma$ is in $\Phi_b$ only for few $p$, by sparseness, and otherwise its weight is $\lfloor a/x_1 \rfloor = \lfloor x b/x_1 \rfloor$. So the factor is $b/p - \lfloor xb/x_1 \rfloor$ when this is positive, that is, for $p$ below about $x_1/x$.
