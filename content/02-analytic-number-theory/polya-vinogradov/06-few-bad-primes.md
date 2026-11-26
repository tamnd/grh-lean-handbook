---
title: Few bad primes, and one good prime
lean:
  - Lib/Analytic/QuadraticTwist.lean
  - New/Reduction/Zeros/Criterion.lean
decls:
  - New.IsPrimeWithTwistZero
  - New.exists_card_zero_quadTwist_le
  - New.IsBadPrime
  - New.zero_density_quadTwist
  - New.exists_entireL_quadTwist_ne_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Few bad primes, and one good prime

This section puts Sections 3 to 5 together. First it counts the primes $d$ for which the twist of one primitive character has a zero in the box. Then it passes from primitive characters to all characters modulo $N$, and it chooses a good prime by Dirichlet's theorem. Throughout, the box is
$$B(\beta, H) = \{s \in \mathbb{C} : \operatorname{Re} s \geq \beta,\ |\operatorname{Im} s| \leq H\}, \qquad \beta = \tfrac12 + 9\delta.$$

### One primitive character

**Definition (A prime with a twisted zero).** Let $\psi$ be a character modulo $N$, let $\beta, H \in \mathbb{R}$, and let $d \in \mathbb{N}$. Then $d$ *has a twisted zero for* $\psi$, $\beta$ and $H$ if $d$ is prime and $L(s, \psi\chi_K) = 0$ for some $s \in B(\beta, H)$, where $\chi_K = (\cdot/d)$.

Lean: `New.IsPrimeWithTwistZero` (Lib/Analytic/QuadraticTwist.lean).

**Lemma (Count for one primitive character).** Let $\delta > 0$, $H \in \mathbb{R}$, and let $\psi$ be a primitive character modulo $M \geq 1$. There is a constant $C$ such that for all sufficiently large $T$ the number of $d \in \{1, \ldots, \lfloor T^2\rfloor\}$ with
$$d \equiv 7 \bmod 8, \qquad \gcd(M, d) = 1, \qquad Md \leq T^2,$$
which have a twisted zero for $\psi$, $1/2 + 9\delta$ and $H$, is at most $C\,T^{2 - \delta}$.

Lean: `New.exists_card_zero_quadTwist_le` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* Let $j \in \{0, 1\}$ be the parity opposite to that of $\psi$: $\psi(-1) = -(-1)^j$. Let $C$ be the constant of the [corollary on sums of theta tails](/decl/New.sum_thetaTailIntegral_le/) for $j$ and $\delta$. Take $T > 0$ large enough for the [theorem on a large tail](/decl/New.eventually_rpow_lt_thetaTailIntegral/) with $j$, $\delta$ and $H$. Put
$$F(v) = J(c_v, T), \qquad c_v(n) = \psi(n)\Bigl(\frac{-v}{n^\circ}\Bigr).$$
Let $d$ be counted. Then $d$ is an odd prime with $d \equiv 3 \bmod 4$, so the twist $\psi\chi_K$ has $\psi\chi_K(-1) = -\psi(-1) = (-1)^j$. It is primitive modulo $Md$ by the [lemma on primitivity](/decl/New.isPrimitive_quadTwist/), and it is not principal by [Lemma](/decl/New.quadTwist_ne_one/). Its conductor is $Md \leq T^2$. Its coefficients are $\psi(n)(n/d) = c_d(n)$ for $n \geq 1$, by the [reciprocity lemma](/decl/New.legendreSym_eq_jacobiSym_ordCompl/). So the theorem on a large tail gives $F(d) > T^{2\delta}$. Since $F \geq 0$,
$$\#\{\text{counted } d\}\cdot T^{2\delta} \leq \sum_{v = 1}^{\lfloor T^2\rfloor}F(v) \leq C\,T^{2 + \delta}.$$
Divide by $T^{2\delta}$. $\square$

The parity $j$ is the same for all counted $d$. This is the reason for the condition $d \equiv 3 \bmod 4$: the corollary of Section 5 is for one fixed $j$. The count also includes the condition $d \leq \lfloor T^2\rfloor$, which follows from $Md \leq T^2$; it is there so that the counted set is a subset of the range of $v$.

### All characters modulo $N$

**Definition (Bad prime).** Let $N \geq 1$, $a \in \mathbb{Z}/N\mathbb{Z}$, $\beta, H \in \mathbb{R}$ and $d \in \mathbb{N}$. Then $d$ is *bad* for $a$, $\beta$ and $H$ if $d \equiv a \bmod N$ and $d$ has a twisted zero for some character $\xi$ modulo $N$, $\beta$ and $H$.

Lean: `New.IsBadPrime` (Lib/Analytic/QuadraticTwist.lean).

The definition is also stated in [the Landau criterion](/chapter/landau-criterion/), where it is used.

**Theorem (Bad primes are rare).** Let $N \geq 1$, $\delta > 0$ and $H \in \mathbb{R}$. Let $a \in \mathbb{Z}/N\mathbb{Z}$ be a class such that every prime $d \equiv a \bmod N$ has $d \equiv 7 \bmod 8$ and $\gcd(N, d) = 1$. Let $B(X)$ be the number of $d \in \{1, \ldots, X\}$ that are bad for $a$, $1/2 + 9\delta$ and $H$. Then, as $X \to \infty$ through $\mathbb{N}$,
$$B(X) = O\bigl(X^{1 - \delta/2}\bigr).$$

Lean: `New.zero_density_quadTwist` (Lib/Analytic/QuadraticTwist.lean).

*Proof.* For each character $\xi$ modulo $N$, [Lemma](/decl/New.exists_isPrimitive_changeLevel_eq/) gives $M_\xi \mid N$ and a primitive character $\psi_\xi$ modulo $M_\xi$ that induces $\xi$. Let $C_\xi$ be the constant of the last lemma for $\psi_\xi$. Put $T = \sqrt{NX}$. For $X$ large, the last lemma holds at $T$ for every $\xi$, since there are finitely many $\xi$.

Let $d \leq X$ be bad, with the character $\xi$ and the zero $s$. By the hypothesis on the class, $d \equiv 7 \bmod 8$ and $\gcd(N, d) = 1$, so $\gcd(M_\xi, d) = 1$, and $M_\xi d \leq NX = T^2$. The twist $\xi\chi_K$ is induced by $\psi_\xi\chi_K$. So
$$L(s, \xi\chi_K) = L(s, \psi_\xi\chi_K)\prod_{p \mid Nd}\bigl(1 - \psi_\xi\chi_K(p)p^{-s}\bigr),$$
and the product does not vanish for $\operatorname{Re} s > 0$, by [Lemma](/decl/New.prod_euler_factor_ne_zero/). So $L(s, \psi_\xi\chi_K) = 0$, and $d$ is counted in the last lemma for $\psi_\xi$. Hence
$$B(X) \leq \sum_\xi C_\xi\,T^{2 - \delta} = \Bigl(\sum_\xi C_\xi\Bigr)N^{1 - \delta/2}\,X^{1 - \delta/2}. \qquad \square$$

**Remark (Formalization).** The name `zero_density_quadTwist` and the phrase "zero density for quadratic twists" in the plan of this handbook suggest a count of zeros. The theorem counts primes, not zeros: a bad prime counts once, however many zeros its twists have in the box. The Lean statement counts all $d \leq X$ that satisfy `IsBadPrime`, and `IsBadPrime` includes primality through `IsPrimeWithTwistZero`. The class hypothesis is stated only for primes; it holds when $8 \mid N$ and $a \equiv 7 \bmod 8$ is prime to $N$, which is the case in the use below. The constant of the $O$ is $(\sum_\xi C_\xi)N^{1 - \delta/2}$, where the $C_\xi$ and the $\psi_\xi$ come from `choose`. It depends on $N$, $\delta$ and $H$, and the source does not compute it. The threshold for $X$ is not explicit either, since it comes from the eventual statement of Section 4.

### The choice of the prime

**Theorem (Choice of the prime).** Let $N \geq 1$, $H \in \mathbb{R}$ and $\beta > 1/2$. Let $a \in (\mathbb{Z}/N\mathbb{Z})^\times$ be a class such that every prime $d \equiv a \bmod N$ has $d \equiv 7 \bmod 8$ and $\gcd(N, d) = 1$. Then there is a prime $d \equiv a \bmod N$ such that
$$\tilde L(s, \xi\chi_K) \neq 0$$
for every character $\xi$ modulo $N$ and every $s$ with $\beta \leq \operatorname{Re} s$ and $|\operatorname{Im} s| \leq H$.

Lean: `New.exists_entireL_quadTwist_ne_zero` (Lib/Analytic/QuadraticTwist.lean).

Here $\tilde L$ is the [entire L-function](/decl/New.entireL/). Since $\xi\chi_K$ is not principal, $\tilde L(s, \xi\chi_K) = L(s, \xi\chi_K)$.

*Proof.* A smaller $\beta$ gives a larger box. So if $\beta \geq 1$, it is sufficient to prove the theorem for $\beta = 3/4$. Assume $\beta < 1$, and write $\beta = 1/2 + 9\delta$ with $0 < \delta < 1/18$. Suppose that every prime $d \equiv a$ fails the conclusion. Then every such prime is bad for $a$, $\beta$ and $H$. Let $f(n) = 1$ if $n$ is a prime $\equiv a \bmod N$, and $f(n) = 0$ otherwise. By the theorem on bad primes, $\sum_{n \leq X}f(n) \leq B(X) = O(X^{1 - \delta/2})$. By partial summation (`LSeriesSummable_of_sum_norm_bigO` (Mathlib)), the series $\sum_n f(n)n^{-\sigma}$ converges absolutely for $\sigma = 1 - \delta/4$. Then $\sum_nf(n)\log n\cdot n^{-1}$ converges (`LSeriesSummable_logMul_of_lt_re` (Mathlib)). This is $\sum_{p \equiv a}\log p/p$. But this series diverges for an invertible class $a$, by Dirichlet's theorem in Mathlib's form `ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div` (Mathlib). This is a contradiction. $\square$

The proof uses the divergence of $\sum_{p \equiv a}\log p/p$, which is weaker than the prime number theorem for progressions. A density $O(X^{1 - \delta/2})$ for the bad primes, against the density $X/(\varphi(N)\log X)$ of all primes of the class, would give much more: almost all primes of the class are good. The source needs one.

### The use in the argument

The only use of this chapter in the files under New/ is in the proof of `New.LFunction_ne_zero_of_primeRemainder_le` (New/Reduction/Zeros/Criterion.lean, line 55), the [one-sided criterion](/chapter/landau-criterion/). There $N = q_0$ is a positive multiple of $8$, $a = d_0$ is a class with $d_0 \equiv 7 \bmod 8$ and $\gcd(d_0, q_0) = 1$, $H = |\operatorname{Im}\rho|$ for the zero $\rho$ to be excluded, and $\beta > 1/2$ is the exponent of the hypothesis. The class condition holds since $8 \mid q_0$: every $d \equiv d_0 \bmod q_0$ has $d \equiv d_0 \equiv 7 \bmod 8$ and $\gcd(d, q_0) = \gcd(d_0, q_0) = 1$. The prime $d$ of the theorem has no twisted zero in the box. So in the region $\operatorname{Re} s > \beta$, $|\operatorname{Im} s| \leq |\operatorname{Im}\rho|$ the residues of the transform of the prime remainder are $n(s)/(\varphi(q_0)s(1 - s))$, with $n(s)$ the sum of the orders of the zeros of the $\tilde L(s, \chi)$, $\chi$ modulo $q_0$. Their sign on the real segment then gives $L(\rho, \psi) \neq 0$ by Landau's lemma, as the chapter on [the Landau criterion](/chapter/landau-criterion/) explains.

The criterion is in turn applied in New/Reduction/OneSidedBound.lean. The theorems `New.polya_vinogradov` and `New.zero_density_quadTwist` are not cited by name in the files under New/; they enter through `New.exists_entireL_quadTwist_ne_zero`.
