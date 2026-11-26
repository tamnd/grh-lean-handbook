---
title: The weights and the remainder
lean:
  - New/Reduction/Zeros/PrimeError.lean
  - Lib/Analytic/EntireLFunction.lean
  - Lib/General/NumberTheory/ImaginaryQuadraticField.lean
decls:
  - New.lambdaKResidueClass
  - New.lambdaKResidueClass_nonneg
  - New.lambdaKSum
  - New.abs_lambdaKSum_exp_le
  - New.entireL
  - New.entireL_ne_zero
  - New.quadTwist
  - New.quadTwist_ne_one
  - New.logDerivMean
  - New.primeRemainder
  - New.abs_primeRemainder_exp_le
  - New.primeRemainder_eq_sum_posPart
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The weights and the remainder

This section defines the objects of the chapter: the weight $\lambda$, its partial sums, the functions $\tilde L$, the twist $\psi\chi_K$, the function $G_q$ and the remainder $R_q$. It proves the bounds that make the transform of Section 5 converge, and the form of $R_q$ that the prime sums use. Throughout, $d$ is a prime, $\chi_K(n) = (n/d)$, and $q \in \mathbb{N}$, with $q \geq 1$ from the definition of $G_q$ on.

### The weight

**Definition (The weight).** For $n \in \mathbb{N}$ let
$$\lambda(n) = \Lambda_{q,1}(n)\bigl(1 - \chi_K(n)\bigr), \qquad \Lambda_{q,1}(n) = \begin{cases} \Lambda(n) & \text{if } n \equiv 1 \bmod q, \\ 0 & \text{otherwise.} \end{cases}$$

Lean: `New.lambdaKResidueClass` (New/Reduction/Zeros/PrimeError.lean), with `ArithmeticFunction.vonMangoldt.residueClass` (Mathlib) for $\Lambda_{q,1}$ and `New.chiK` (Lib/General/NumberTheory/ImaginaryQuadraticField.lean) for $\chi_K$.

**Lemma (Bounds for the weight).** For every $n \in \mathbb{N}$, $0 \leq 1 - \chi_K(n) \leq 2$, and
$$0 \leq \lambda(n) \leq 2\Lambda(n) \leq 2\log n \leq 2n.$$

Lean: `New.lambdaKResidueClass_nonneg` (New/Reduction/Zeros/PrimeError.lean), with `New.one_sub_chiK_mem_Icc`, `New.lambdaKResidueClass_le_two_mul_vonMangoldt`, `New.lambdaKResidueClass_le_two_mul` and `New.lambdaKResidueClass_nonneg_and_abs_le`.

*Proof.* The Legendre symbol takes the values $0$, $1$ and $-1$. So $1 - \chi_K(n) \in \{1, 0, 2\}$. Also $0 \leq \Lambda_{q,1}(n) \leq \Lambda(n) \leq \log n$, and $\log n \leq n$. Multiply. $\square$

Take $q = 1$. If $(p/d) = 1$, then $\lambda(p^k) = 0$ for all $k$. If $(p/d) = -1$, then $\lambda(p^k)$ is $2\log p$ for odd $k$ and $0$ for even $k$. Also $\lambda(d^k) = \log d$. For $d \equiv 7 \bmod 8$, quadratic reciprocity shows that the weight sees the inert primes of $K$ with weight $2$, the ramified prime $d$ with weight $1$, and not the split primes, $2$ among them.

### The partial sums

**Definition (Partial sums).** For $r \in \mathbb{N}$ and real $y$ let
$$\Sigma_r(y) = y^{-r} \sum_{1 \leq n \leq y} \lambda(n)\, n^{r - 1}.$$

Lean: `New.lambdaKSum` (New/Reduction/Zeros/PrimeError.lean).

The source uses $r = 0$ and $r = 1$: $\Sigma_0(y) = \sum_{n \leq y} \lambda(n)/n$ and $\Sigma_1(y) = y^{-1}\sum_{n \leq y} \lambda(n)$. Their difference is the weighted sum $\sum_{n \leq y} \lambda(n)(1/n - 1/y)$.

**Lemma (Growth of the partial sums).** For every $r \in \mathbb{N}$ and every real $v$, $|\Sigma_r(e^v)| \leq 2e^v$.

Lean: `New.abs_lambdaKSum_exp_le` (New/Reduction/Zeros/PrimeError.lean).

*Proof.* The sum has at most $e^v$ terms. By the lemma above, each term satisfies $0 \leq \lambda(n) n^{r - 1} \leq 2n^r \leq 2e^{rv}$. So the sum is at most $2e^v e^{rv}$, and $\Sigma_r(e^v) \leq 2e^v$. $\square$

### The entire L-functions and the twists

**Definition (The entire L-function).** Let $\chi$ be a Dirichlet character modulo $N \geq 1$. Put $\tilde L(s, \chi) = L(s, \chi)$ if $\chi$ is not principal. If $\chi$ is principal, let $\tilde L(s, \chi)$ be the entire function that equals $(s - 1)L(s, \chi)$ for $s \neq 1$.

Lean: `New.entireL` (Lib/General/NumberTheory/ImaginaryQuadraticField.lean), with `DirichletCharacter.LFunctionTrivChar₁` (Mathlib) for the principal case and `New.analyticAt_entireL` (Lib/Analytic/EntireLFunction.lean).

For $N = 1$, $\tilde L(s, 1) = (s - 1)\zeta(s)$ is the function $Z$ of Section 2. For a principal $\chi_0$ modulo $N$, $\tilde L(s, \chi_0) = (s - 1)\zeta(s)\prod_{p \mid N}(1 - p^{-s})$, so in $\operatorname{Re} s > 0$ its zeros are the zeros of $\zeta$.

**Lemma (Non-vanishing on the line 1).** Let $\chi$ be a Dirichlet character modulo $N \geq 1$, and let $\operatorname{Re} s \geq 1$. Then $\tilde L(s, \chi) \neq 0$.

Lean: `New.entireL_ne_zero` (Lib/Analytic/EntireLFunction.lean).

*Proof.* For $\operatorname{Re} s \geq 1$ and $s \neq 1$, Mathlib proves $L(s, \chi) \neq 0$. At $s = 1$, a non-principal $\chi$ has $L(1, \chi) \neq 0$ (Dirichlet), and for the principal character the value of $\tilde L$ at $1$ is the residue of $L(s, \chi_0)$, which is $\prod_{p \mid N}(1 - 1/p) \neq 0$. $\square$

The classical sources are Davenport, Chapters 1 and 4, for $L(1, \chi) \neq 0$, and Chapters 13 and 14 for the line $\operatorname{Re} s = 1$.

**Definition (The twist by χ_K).** Let $\psi$ be a Dirichlet character modulo $N$. The *twist* $\psi\chi_K$ is the product of the characters that $\psi$ and $\chi_K$ induce modulo $Nd$. Its value at $n \in \mathbb{Z}$ is $\psi(n)(n/d)$.

Lean: `New.quadTwist` (Lib/General/NumberTheory/ImaginaryQuadraticField.lean), with `New.quadTwist_apply` (Lib/Analytic/EntireLFunction.lean) for the value.

**Lemma (The twist is not principal).** Let $d$ be an odd prime, and let $\psi$ be a character modulo $N$ with $\gcd(N, d) = 1$. Then $\psi\chi_K$ is not the principal character modulo $Nd$.

Lean: `New.quadTwist_ne_one` (Lib/Analytic/EntireLFunction.lean).

*Proof.* Since $d$ is odd, there is a non-residue $a$ modulo $d$. By the Chinese remainder theorem there is $n$ with $n \equiv 1 \bmod N$ and $n \equiv a \bmod d$. Then $(\psi\chi_K)(n) = \psi(1)(a/d) = -1$. The principal character takes only the values $0$ and $1$. $\square$

For $d = 2$ the lemma fails: the Legendre symbol modulo $2$ is the principal character modulo $2$ (Exercise 5). This is why the results from Section 4 on ask $d \neq 2$.

### The function G_q and the remainder

**Definition (The mean of logarithmic derivatives).** Let $q \geq 1$. For $s \in \mathbb{C}$ let
$$G_q(s) = \frac{1}{\varphi(q)}\Bigl(\sum_{\psi \bmod q}\Bigl(\frac{\tilde L'}{\tilde L}(s, \psi\chi_K) - \frac{\tilde L'}{\tilde L}(s, \psi)\Bigr) - 1\Bigr),$$
where $\psi$ runs over the characters modulo $q$ and the prime denotes $\partial/\partial s$.

Lean: `New.logDerivMean` (New/Reduction/Zeros/PrimeError.lean).

Away from the zeros of the $\tilde L$, $\varphi(q)G_q = \mathcal{L}_K'/\mathcal{L}_K - \mathcal{L}'/\mathcal{L} - 1$, where $\mathcal{L}(s) = \prod_\psi \tilde L(s, \psi)$ and $\mathcal{L}_K(s) = \prod_\psi \tilde L(s, \psi\chi_K)$. So $G_q$ is meromorphic on $\mathbb{C}$. Section 4 explains the term $-1$.

**Remark (Formalization).** The source defines $G_q$ with Mathlib's `logDeriv f s`, which is $f'(s)/f(s)$ with the convention $x/0 = 0$. So $G_q$ is a function $\mathbb{C} \to \mathbb{C}$ with arbitrary values at the zeros of the $\tilde L$. No statement depends on these values. The source uses $G_q$ only where it is analytic ($\operatorname{Re} s \geq 1$), and through limits of $(z - \rho)G_q(z)$ as $z \to \rho$ with $z \neq \rho$.

**Definition (The weighted prime remainder).** Let $q \geq 1$, and put $c_q = \operatorname{Re} G_q(1)$. For real $x$ let
$$R_q(x) = \Sigma_0(x) - \Sigma_1(x) - \frac{\log x}{\varphi(q)} - c_q = \sum_{1 \leq n \leq x} \lambda(n)\Bigl(\frac{1}{n} - \frac{1}{x}\Bigr) - \frac{\log x}{\varphi(q)} - c_q.$$

Lean: `New.primeRemainder` (New/Reduction/Zeros/PrimeError.lean).

By [Lemma](/decl/New.entireL_ne_zero/), $G_q$ is analytic at $1$, so $c_q$ is a real number. Section 5 proves that $G_q(1)$ is real when $d$ is odd and prime to $q$ ([Proposition](/decl/New.ofReal_re_logDerivMean_one/)). So the real part in the definition loses nothing.

**Remark (Formalization).** The definition is a formula for every real $x$. For $x < 1$ the sum is empty, Mathlib's $\log x$ is $\log |x|$, and $\Sigma_1(0)$ is a division by $0$, of value $0$. These values have no meaning. The source uses $R_q(x)$ only at $x = e^v$ with $v \geq 0$ and at large $x$.

### Bounds and the form with positive parts

**Lemma (Growth of the remainder).** Let $q \geq 1$ and $v \geq 0$. Then $|R_q(e^v)| \leq (|c_q| + 5)\, e^v$.

Lean: `New.abs_primeRemainder_exp_le` (New/Reduction/Zeros/PrimeError.lean).

*Proof.* By the triangle inequality, $|R_q(e^v)| \leq |\Sigma_0(e^v)| + |\Sigma_1(e^v)| + v/\varphi(q) + |c_q|$. By [Lemma](/decl/New.abs_lambdaKSum_exp_le/) the first two terms are at most $2e^v$ each. Also $v/\varphi(q) \leq v \leq e^v$, and $|c_q| \leq |c_q|e^v$ since $v \geq 0$. $\square$

**Lemma (The form with positive parts).** Let $z > 0$, and let $A \in \mathbb{N}$ with $\lfloor z \rfloor \leq A$. Then
$$R_q(z) = \sum_{n = 1}^{A} \lambda(n)\Bigl(\frac{1}{n} - \frac{1}{z}\Bigr)^{+} - \frac{\log z}{\varphi(q)} - c_q,$$
where $t^+ = \max(t, 0)$. If $A \geq z$, then also $R_q(z) = A^{-1}\sum_{n = 1}^{A} \lambda(n)(A/n - A/z)^+ - \log z/\varphi(q) - c_q$.

Lean: `New.primeRemainder_eq_sum_posPart` (New/Reduction/Zeros/PrimeError.lean), and `New.primeRemainder_eq_sum` for the second form.

*Proof.* For $n \leq z$ the positive part is $1/n - 1/z$. For $n > z$ it is $0$. The second form is the first one, multiplied and divided by $A$. $\square$

The prime sums of the lattice argument use the second form ([prime sums and the total remainder](/chapter/prime-sums/)).

**Example (The remainder for d = 7).** Take $d = 7$ and $q = 1$. Section 4 gives $c_1 = -1.561580$ to six decimals. The squares modulo $7$ are $1, 2, 4$. So $2$ splits, $3$ and $5$ are inert, and the weights of $n \leq 10$ are $\lambda(3) = 2\log 3$, $\lambda(5) = 2\log 5$ and $\lambda(7) = \log 7$. The powers $2, 4, 8$ of the split prime $2$ and the square $9$ of the inert prime $3$ have weight $0$. So
$$\sum_{n \leq 10} \lambda(n)\Bigl(\frac{1}{n} - \frac{1}{10}\Bigr) = 2\log 3 \cdot \frac{7}{30} + 2\log 5 \cdot \frac{1}{10} + \log 7 \cdot \frac{3}{70} = 0.917970,$$
and $R_1(10) = 0.917970 - \log 10 + 1.561580 = 0.176965$. A computation with all prime powers up to $10^6$ gives these values:

| $x$ | $10$ | $10^2$ | $10^3$ | $10^4$ | $10^5$ | $10^6$ |
|---|---|---|---|---|---|---|
| $R_1(x)$ | $0.17696$ | $0.00722$ | $0.00015$ | $0.00063$ | $0.00011$ | $-0.00008$ |

The values are small, as the prime number theorem for $R_q$ predicts, and they change sign. Each zero $\rho$ of $\zeta$ gives a term $x^{\rho - 1}/(\rho(1 - \rho))$, and each zero of $L(s, \chi_K)$ a term $-x^{\rho - 1}/(\rho(1 - \rho))$ (Section 5).
