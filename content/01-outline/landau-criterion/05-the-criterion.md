---
title: The criterion
lean:
  - Lib/Analytic/QuadraticTwist.lean
  - New/Reduction/Zeros/Criterion.lean
  - New/Reduction/OneSidedBound.lean
decls:
  - New.IsBadPrime
  - New.zero_density_quadTwist
  - New.exists_entireL_quadTwist_ne_zero
  - New.LFunction_ne_zero_of_primeRemainder_le
  - New.eventually_primeRemainder_le_rpow
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The criterion

Section 4 showed what the criterion needs: a prime $d$ whose twists have no zeros at the point $\rho$ and on the real segment to the right of $\beta$. This section states the theorem that gives such a $d$, proves the criterion, and shows how the proof of the main theorem applies it.

### A prime with no twisted zeros in a box

Fix a modulus $N \geq 1$ and a class $a$ modulo $N$. Suppose that every prime $d$ of the class $a$ satisfies $d \equiv 7 \bmod 8$ and $(d, N) = 1$. This holds if $8 \mid N$, $a \equiv 7 \bmod 8$ and $(a, N) = 1$. For real $\beta$ and $H$, the *box* is the set of $s$ with $\operatorname{Re} s \geq \beta$ and $|\operatorname{Im} s| \leq H$.

**Definition (Bad prime).** A number $d$ is *bad* for $a$, $\beta$ and $H$ if $d \equiv a \bmod N$, $d$ is prime, and for some character $\xi$ modulo $N$ the function $L(s, \xi\chi_K)$, with $\chi_K = (\cdot / d)$, has a zero in the box.

Lean: `New.IsBadPrime` (Lib/Analytic/QuadraticTwist.lean).

**Theorem (Bad primes are rare).** Let $\delta > 0$, let $H$ be real, and let $a$ be a class modulo $N$ whose primes are all $\equiv 7 \bmod 8$ and prime to $N$. Let $B(X)$ be the number of integers $d \in (0, X]$ that are bad for $a$, $\beta = 1/2 + 9\delta$ and $H$. Then
$$B(X) = O\bigl(X^{1 - \delta/2}\bigr) \qquad (X \to \infty,\ X \in \mathbb{N}).$$

Lean: `New.zero_density_quadTwist` (Lib/Analytic/QuadraticTwist.lean).

The implied constant depends on $N$, $\delta$ and $H$. [Pólya-Vinogradov and quadratic twists](/chapter/polya-vinogradov/) in Volume 2 proves the theorem. In outline: a zero in the box makes an integral of theta series of the twist large, by the three lines theorem, and the mean square of these theta series over $d$ is small, by Pólya-Vinogradov for Jacobi symbols. The congruence $d \equiv 7 \bmod 8$ fixes the parity of the twists and gives the reciprocity $(n/d) = (-d/n')$, with $n'$ the odd part of $n$.

**Theorem (Choice of the prime).** Let $a$ be an invertible class modulo $N$ whose primes are all $\equiv 7 \bmod 8$ and prime to $N$. Let $\beta > 1/2$ and let $H$ be real. Then there is a prime $d \equiv a \bmod N$ such that
$$E_{\xi\chi_K}(s) \neq 0$$
for every character $\xi$ modulo $N$ and every $s$ with $\beta \leq \operatorname{Re} s$ and $|\operatorname{Im} s| \leq H$. Here $\chi_K = (\cdot / d)$.

Lean: `New.exists_entireL_quadTwist_ne_zero` (Lib/Analytic/QuadraticTwist.lean).

The twists $\xi\chi_K$ are not principal, so $E_{\xi\chi_K}$ is $L(s, \xi\chi_K)$ (Section 4).

*Proof.* A box for a smaller $\beta$ contains the box for a larger one. So it is sufficient to prove the theorem for $\beta < 1$, and for $\beta \geq 1$ to use $\beta = 3/4$. Write $\beta = 1/2 + 9\delta$, with $0 < \delta < 1/18$. Suppose that every prime of the class is bad. Then the number of primes $p \leq X$ of the class is at most $B(X) = O(X^{1 - \delta/2})$, by the theorem on bad primes. By partial summation, the series $\sum_p p^{-\sigma}$ over the primes of the class converges for $\sigma = 1 - \delta/4$. So $\sum_p (\log p)/p$ over the class converges, since $\log p \ll p^{\delta/4}$. But this series diverges, by Dirichlet's theorem for the invertible class $a$. This is a contradiction. So some prime $d$ of the class is not bad, and for this $d$ no $L(s, \xi\chi_K)$ vanishes in the box. $\square$

**Remark (Formalization).** The source states the zero density input in this weak form: one good prime in each class, for each box. The classical zero density theorems for quadratic twists count zeros, with explicit exponents. The source cites Jutila (1975) and Heath-Brown (1995) with no theorem numbers (see the notes), and it replaces Heath-Brown's quadratic large sieve by a weaker mean value estimate. No person has checked that the weak form follows the cited works. For this chapter that does not matter: the criterion uses only the statement above, and Lean checks the statement from its proof, if the reported checks hold. The final step of the proof uses Dirichlet's theorem in the form that $\sum (\log p)/p$ diverges over an invertible class. So the prime number theorem for progressions is not used.

### The one-sided criterion

**Theorem (One-sided criterion).** Let $q_0 \geq 1$ with $8 \mid q_0$. Let $d_0 \geq 0$ be an integer with $d_0 \equiv 7 \bmod 8$ and $(d_0, q_0) = 1$, and let $\beta > 1/2$. Suppose that for every prime $d \equiv d_0 \bmod q_0$ the remainder $R_{q_0}$ of $d$ and $q_0$ satisfies
$$R_{q_0}(x) \leq x^{\beta - 1} \qquad \text{for all large real } x.$$
Then $L(\rho, \psi) \neq 0$ for every Dirichlet character $\psi$ modulo $q_0$ and every $\rho \neq 1$ with $\operatorname{Re} \rho > \beta$.

Lean: `New.LFunction_ne_zero_of_primeRemainder_le` (New/Reduction/Zeros/Criterion.lean).

The conclusion excludes $\rho = 1$ for every $\psi$, also for the characters that are not principal. For those, $L(1, \psi) \neq 0$ is classical, and the proof of the main theorem takes it from Mathlib.

*Proof.* Fix $\psi$ and $\rho$. Let $H = |\operatorname{Im} \rho|$.

Step 1: the class. Let $d$ be a prime with $d \equiv d_0 \bmod q_0$. Since $8 \mid q_0$, we get $d \equiv d_0 \equiv 7 \bmod 8$. Since $(d_0, q_0) = 1$, we get $(d, q_0) = 1$. So the class $a = d_0 \bmod q_0$ is invertible, and all its primes are $\equiv 7 \bmod 8$ and prime to $q_0$.

Step 2: the choice of $d$. By the theorem on the choice of the prime, with $N = q_0$, $\beta$ and $H$, there is a prime $d \equiv d_0 \bmod q_0$ such that $E_{\xi\chi_K}(s) \neq 0$ for all $\xi$ modulo $q_0$ and all $s$ with $\beta \leq \operatorname{Re} s$ and $|\operatorname{Im} s| \leq H$. In the notation of Section 4, $n'(s) = 0$ for these $s$, by the equivalence of $\operatorname{ord}_s E = 0$ and $E(s) \neq 0$ (Lean: `New.analyticOrderNatAt_entireL_eq_zero_iff`). Fix this $d$ from now on.

Step 3: the polar pair. By Step 1, $d \equiv 7 \bmod 8$ and $(d, q_0) = 1$. By the theorem on the polar pair of the remainder in Section 4, the pair $(E, r)$ with $E(v) = R_{q_0}(e^v)$ is polar, and for $\operatorname{Re} s > \beta$ and $|\operatorname{Im} s| \leq H$,
$$r(s) = \frac{n(s)}{\varphi(q_0)\, s\, (1 - s)},$$
with the value $0$ at $s = 1$ (Section 4).

Step 4: the sign. Let $x > \beta$ be real. Then $|\operatorname{Im} x| = 0 \leq H$, so Step 3 applies, and $r(x)$ is real. If $x \leq 1$, then $x(1 - x) \geq 0$ and $n(x) \geq 0$, so $r(x) \geq 0$. Here $x > \beta > 1/2 > 0$. At $x = 1$ the quotient is a division by $0$, and its value is $0$. If $x \geq 1$, then $E_\chi(x) \neq 0$ for every $\chi$ (Lean: `New.entireL_ne_zero`), so $n(x) = 0$ and $r(x) = 0$. In all cases $\operatorname{Re} r(x) \geq 0$.

Step 5: the bound. By hypothesis, for this $d$, $R_{q_0}(x) \leq x^{\beta - 1}$ for all large $x$. With $x = e^v$ this is $E(v) \leq e^{(\beta - 1)v}$ for all large $v$.

Step 6: Landau's lemma. We have $\beta > 0$, the sign of Step 4, the bound of Step 5, and $\operatorname{Re} \rho > \beta$. So [Theorem](/decl/New.IsPolar.landau/) of Section 3 gives $r(\rho) = 0$.

Step 7: the conclusion. The point $\rho$ satisfies $\operatorname{Re} \rho > \beta$ and $|\operatorname{Im} \rho| = H$, so Step 3 gives
$$0 = r(\rho) = \frac{n(\rho)}{\varphi(q_0)\, \rho\, (1 - \rho)}.$$
Here $\rho \neq 0$ since $\operatorname{Re} \rho > 0$, $\rho \neq 1$ by hypothesis, and $\varphi(q_0) \neq 0$. So $n(\rho) = 0$. The orders are natural numbers, so $\operatorname{ord}_\rho E_\psi = 0$, and $E_\psi(\rho) \neq 0$. If $\psi$ is not principal, $E_\psi(\rho) = L(\rho, \psi)$. If $\psi$ is principal, $E_\psi(\rho) = (\rho - 1)L(\rho, \psi)$, since $\rho \neq 1$. In both cases $L(\rho, \psi) \neq 0$. $\square$

**Remark (Formalization).** The hypothesis is a family of statements, one for each prime $d \equiv d_0 \bmod q_0$, each with its own threshold for "large $x$". The proof uses only one of them. At $x = 1$ in Step 4 the junk value $r(1) = 0$ is also the true value, since the definition of a polar pair forces $r(1) = \lim_{z \to 1}(z - 1)\Phi(z) = 0$. The value $L(1, \psi)$ for the principal character is a junk value in Mathlib, so the hypothesis $\rho \neq 1$ is needed for the conversion from $E_\psi$ to $L$ in Step 7. The hypothesis $\beta > 1/2$ is used only in Step 2. Landau's lemma in Step 6 needs only $\beta > 0$ (Section 3).

### One prime is enough, and every prime is needed

The proof uses the bound for one prime $d$. This is enough because Landau's lemma needs the sign of the residues only on the real half-line $(\beta, \infty)$, and it gives information at one point $\rho$. The box $\operatorname{Re} s \geq \beta$, $|\operatorname{Im} s| \leq |\operatorname{Im} \rho|$ contains both. Zeros of the twists at other places give poles that the lemma does not look at.

The proof needs the bound for every prime of the class, for two reasons.

- The prime $d$ depends on $\rho$. The box grows with $|\operatorname{Im} \rho|$, and the theorem on the choice of the prime gives a good prime for each box. It does not give one prime that is good for all boxes. That would be a statement that some $L(s, \xi\chi_K)$ has no zeros in all of $\operatorname{Re} s \geq \beta$, which is the Riemann hypothesis for the twists in this half-plane.
- The prime $d$ is not explicit. The proof of the choice of the prime is by contradiction. It shows that not all primes of the class are bad, and it does not say which prime is good.

So the later chapters prove the bound for every prime $d$ of the class. Only the eventual bound is used, so the threshold for "large $x$" may depend on $d$, and no uniformity in $d$ is needed.

### The application in the main theorem

The proof of the main theorem applies the criterion with a special modulus. Here is the input from [the main inequality and the end of the proof](/chapter/main-inequality/).

**Theorem (One-sided bound).** Let $q_0 \geq 1$ be a multiple of $18480$, let $d$ be a prime with $d \equiv q_0/2 - 1 \bmod q_0$, and let $\varepsilon > 0$. Then the remainder $R_{q_0}$ of $d$ and $q_0$ satisfies
$$R_{q_0}(y) \leq y^{-1/2 + \varepsilon} \qquad \text{for all large real } y.$$

Lean: `New.eventually_primeRemainder_le_rpow` (New/Reduction/OneSidedBound.lean).

The theorem [`New.grh`](/decl/New.grh/) says that $L(s, \chi) \neq 0$ for every modulus $q \geq 1$, every character $\chi$ modulo $q$, and every $s$ with $\operatorname{Re} s > 1/2$, except $s = 1$ for the principal character. Its proof from the two theorems above has these steps. Let $\rho$ satisfy the hypotheses.

1. If $\rho = 1$, then $\chi$ is not principal, and $L(1, \chi) \neq 0$ by the classical theorem of Dirichlet (Mathlib).
2. If $\rho \neq 1$, choose $\beta$ with $1/2 < \beta < \operatorname{Re} \rho$. Let $q_0 = 18480\, q$ and $d_0 = 9240\, q - 1$. Then $q_0 = 2(d_0 + 1)$, and $d_0 = q_0/2 - 1$.
3. The hypotheses on $q_0$ and $d_0$. We have $18480 = 2^4 \cdot 3 \cdot 5 \cdot 7 \cdot 11$, so $8 \mid q_0$. We have $9240 = 8 \cdot 1155$, so $d_0 \equiv -1 \equiv 7 \bmod 8$. A common divisor of $d_0$ and $q_0 = 2(d_0 + 1)$ divides $2(d_0 + 1) - 2d_0 = 2$, and $d_0$ is odd, so $(d_0, q_0) = 1$.
4. The hypothesis on $R_{q_0}$. Let $d$ be a prime with $d \equiv d_0 \bmod q_0$. The theorem on the one-sided bound, with $\varepsilon = \beta - 1/2 > 0$, gives $R_{q_0}(x) \leq x^{-1/2 + (\beta - 1/2)} = x^{\beta - 1}$ for all large $x$.
5. The criterion gives $L(\rho, \psi) \neq 0$ for the character $\psi$ modulo $q_0$ induced by $\chi$.
6. The functions $L(s, \psi)$ and $L(s, \chi)$ differ by the factor $\prod_{p \mid q_0,\ p \nmid q}(1 - \chi(p)p^{-s})$. Each factor is not $0$ for $\operatorname{Re} s > 0$. So $L(\rho, \chi) \neq 0$.

The numbers $18480$ and $9240$ come from the lattice part of the proof, not from this chapter. The criterion needs only $8 \mid q_0$ and $d_0 \equiv 7 \bmod 8$ prime to $q_0$. [Fields, places and twists](/chapter/fields-places-twists/) explains the parameters $q_0$ and $d$ of that part.

**Remark (Formalization).** In step 6 the source uses the Mathlib identity for the L-function of an induced character. Its hypothesis, $\chi \neq 1$ or $s \neq 1$, is the hypothesis of the main theorem at $\rho$.
