---
title: Primes in windows
lean:
  - Lib/Analytic/Primes.lean
  - Lib/Analytic/PrimeNumberTheorem/ZeroFreeRegion.lean
decls:
  - New.exists_prime_modEq_one_log_mem
  - New.factorsThrough_sq_of_sq_eq_one
  - New.eventually_norm_logDeriv_entireL_le_near_one
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Primes in windows

The data need three primes $\equiv 1$ modulo $q_2^2 = (q_0 d)^{2(s + 6)}$, with prescribed sizes. The modulus grows with $x$. This section states the theorem that the source proves for this purpose, compares it with the Siegel-Walfisz theorem, and explains why the weak form is enough. The proof is given in outline. Volume 2 gives it in full in [primes in windows](/chapter/primes-in-windows/).

### The textbook theorem

Let $\psi(x; q, a) = \sum_{n \leq x,\ n \equiv a \ (q)} \Lambda(n)$, where $\Lambda$ is the von Mangoldt function.

**Theorem (Siegel-Walfisz).** Let $A > 0$. There is a constant $c > 0$ such that
$$\psi(x; q, a) = \frac{x}{\varphi(q)} + O_A\Bigl(x \exp\bigl(-c\sqrt{\log x}\bigr)\Bigr)$$
for all $x \geq 2$, all $q \leq (\log x)^A$, and all $a$ prime to $q$. The implied constant depends on $A$, and it is not effective.

Not in the source. The source proves only the special case `New.exists_prime_modEq_one_log_mem` (Lib/Analytic/Primes.lean), for moduli $Q^k$, where the real characters come from the fixed modulus $Q^2$ and no Siegel zero occurs.

This is the form of Montgomery and Vaughan, *Multiplicative Number Theory I*, Corollary 11.19, which the source cites. The ineffective constant comes from Siegel's theorem on exceptional zeros. For a fixed modulus the theorem is the prime number theorem for progressions, with the classical error term.

### The source form

**Theorem (Primes $\equiv 1$ modulo $Q^k$ in a window).** Let $Q, A \in \mathbb{N}$ with $Q \neq 0$ and $4 \mid Q$. For every large real $W$ the following holds. For every $k \in \mathbb{N}$ with $k > 1$ and $Q^k \leq W^A$, and every real $U$ with $W \leq U \leq W^A$, there is a prime $p$ with
$$p \equiv 1 \pmod{Q^k} \qquad\text{and}\qquad U \leq \log p \leq U + W.$$
Lean: `New.exists_prime_modEq_one_log_mem` (Lib/Analytic/Primes.lean).

Lean writes `M` for the number $Q$. This book writes $Q$, since $M = p_0 p_1$ is the principal level of the data.

The phrase "for every large real $W$" means that there is a threshold $W_0(Q, A)$, and the statement holds for $W \geq W_0$. The theorem follows from the Siegel-Walfisz theorem. Put $X = e^U$, so that $W \leq \log X$ and $Q^k \leq W^A \leq (\log X)^A$. The theorem with $q = Q^k$ and $a = 1$ gives
$$\psi(Xe^W; q, 1) - \psi(X; q, 1) = \frac{X(e^W - 1)}{\varphi(q)} + O\Bigl(Xe^W \exp\bigl(-c\sqrt{U}\bigr)\Bigr),$$
and the main term wins for large $W$, since $\varphi(q) \leq W^A$ and $\exp(-c\sqrt{U}) \leq \exp(-c\sqrt{W})$. The prime powers $p^j$ with $j \geq 2$ contribute $O(\sqrt{Xe^W}\log(Xe^W))$, which is smaller. So the window $[X, Xe^W]$ contains a prime $\equiv 1 \pmod{q}$.

**Remark (How weak the source form is).** Next to the Siegel-Walfisz theorem the source form is weak in five ways.

1. It finds one prime, and gives no count.
2. It treats only the class $a = 1$.
3. It treats only moduli $Q^k$, powers of one fixed multiple of $4$.
4. The window is long. In multiplicative terms it is $[e^U, e^{U + W}]$, and the ratio $e^W$ of its ends is larger than any fixed power of $U$, since $U \leq W^A$. A short interval theorem would ask for a prime in $[X, X + X^\theta]$ with $\theta < 1$; this window is the opposite.
5. The threshold $W_0$ is not explicit.

The range of moduli is the Siegel-Walfisz range: $q = Q^k \leq W^A \leq (\log p)^A$.

**Remark (Why the weak form is enough).** The data ask for three windows. In each case the modulus is $q_2^2 = (q_0 d)^{2(s+6)}$, and the theorem applies with $Q = q_0 d$, which is divisible by $4$, and $k = 2(s + 6) > 1$. The scale is $W = x^{\varepsilon/6}$, and the exponent is $A = n + 7$, with $n$ the fixed exponent of [the large scales](/decl/New.Parameters.IsLargeScale/). Section 5 shows the following.

- The modulus is small: $q_2^2 \leq W^n \leq W^{n + 7}$. This is the condition $99\, q_0 d \log x \leq n \log W$ of the large scales, together with $s \leq 32\log x$.
- The windows start at points $U$ with $\log b \leq U \leq 24 m \log b$, and $[\log b, 24 m \log b] \subseteq [W, W^{n + 7}]$. Indeed $\log b \geq W^6 \geq W$, $m \leq 2^s \leq W^n$ and $24 \log b \leq W^7$.
- For $p_0$ and $p_1$ the source needs $h + 1$ disjoint windows of length $W$ inside $[10 \log b, 11 \log b]$, where $h$ is the class number of $K$. They exist, since $(2h + 2) W \leq W^2 \leq \log b$.
- For $N$ the source needs a window of length $\sqrt{\log b}$. A window of length $W$ is shorter, since $W^2 \leq W^6 \leq \log b$.

So the data need only one prime in each of a few windows of length $W$ at height at least $W^6$, for a modulus that is polynomial in $W$. The finding F-097 of the [register of findings](/chapter/register-of-findings/) asks whether the uniformity of the theorem is what the data need. The proof of [the existence theorem](/decl/New.eventually_exists_data/) applies this theorem to exactly these windows, and Lean accepts the composition, if the reported checks hold.

### No exceptional zero

The Siegel-Walfisz theorem is hard because of a possible real zero of $L(s, \chi)$ near $1$ for a real character $\chi$ to a large modulus. The source avoids this problem with an algebraic observation: for the moduli $Q^k$, the real characters all come from the fixed modulus $Q^2$.

**Lemma (Real characters come from $Q^2$).** Let $Q \neq 0$ with $4 \mid Q$, let $k \geq 2$, and let $\chi$ be a Dirichlet character modulo $Q^k$ with $\chi^2 = 1$. Then $\chi$ factors through the modulus $Q^2$: it is induced from a character modulo $Q^2$.
Lean: `New.factorsThrough_sq_of_sq_eq_one` (Lib/Analytic/Primes.lean).

*Proof.* It is enough to show that every unit $u \equiv 1 \pmod{Q^2}$ is a square modulo $Q^k$. Then $\chi(u) = \chi(c)^2 = \chi^2(c) = 1$ for such $u$, so $\chi$ is trivial on the kernel of the reduction to $Q^2$. Write $u = 1 + 4c_0$ with $Q^2/4 \mid c_0$. One looks for $c$ with $(1 + 2c)^2 = 1 + 4(c^2 + c) \equiv u$, that is, $c^2 + c \equiv c_0 \pmod{Q^k/4}$. The polynomial $f(c) = c^2 + c - c_0$ has $f(0) = -c_0 \equiv 0$ modulo $Q^2/4$ and $f'(0) = 1$, a unit. Newton's iteration $c \mapsto c - f(c)/f'(c)$ lifts the root modulo $Q^2/4$ to a root modulo every power of $Q$ that divides $Q^k/4$. $\square$

There are only finitely many characters modulo $Q^2$. For each real one, $L(1, \chi) \neq 0$, and by continuity $|L(s, \chi)|$ is bounded below on a small disc about $1$. This lower bound is uniform in $k$. Indeed a character modulo $Q^k$ with $\chi^2 = 1$ is induced from a character $\chi_0$ modulo $Q^2$, and since $Q^k$ and $Q^2$ have the same prime factors, $L(s, \chi) = L(s, \chi_0)$. For the other characters the classical zero-free region applies, with no exception.

To state the result, let $L^\ast(s, \chi)$ be $L(s, \chi)$ if $\chi$ is not principal, and the entire function $(s - 1) L(s, \chi)$ if $\chi$ is principal.

**Lemma (No zeros near $1$).** Let $A \in \mathbb{N}$ and $Q \neq 0$ with $4 \mid Q$. For every large real $X$ the following holds. For every $k > 1$ with $Q^k \leq X^A$, every Dirichlet character $\chi$ modulo $Q^k$, and every $s \in \mathbb{C}$ with $|s - 1| \leq 1/X$,
$$L^\ast(s, \chi) \neq 0 \qquad\text{and}\qquad \Bigl| \frac{(L^\ast)'}{L^\ast}(s, \chi) \Bigr| \leq X.$$
Lean: `New.eventually_norm_logDeriv_entireL_le_near_one` (Lib/Analytic/Primes.lean).

*Proof.* The source applies its zero-free region, from the chapter on the [prime number theorem](/chapter/prime-number-theorem/) in Volume 2, with the parameter $l = (A + 1)\log X$. That result gives, for a character to a modulus $N \leq e^l$ and for $\operatorname{Re} s \geq 1 - l^{-25}$, $|s| \leq e^l$, that $L^\ast(s, \chi) \neq 0$ and $|(L^\ast)'/L^\ast| \leq 2 l^{25}$, provided that for each real character $|L(z,\chi)|$, with the pole removed, is at least $1/l$ on $|z - 1| \leq 1/l$. The proviso holds for large $X$ by the lemma on real characters and the finiteness of the characters modulo $Q^2$. The disc $|s - 1| \leq 1/X$ lies in the region for large $X$, and $2 l^{25} = 2 (A + 1)^{25} (\log X)^{25} \leq X$. $\square$

The zero-free region of the source is proved by the classical $3$-$4$-$1$ inequality; see Montgomery and Vaughan, Chapter 11. The threshold for $X$ depends on the lower bounds for the finitely many $L(1, \chi)$ with $\chi$ real modulo $Q^2$. It exists, but the source does not compute it.

### Newman's argument

The source proves the theorem on windows by the contour method that Newman used for the prime number theorem. It needs only the disc of the last lemma, not a zero-free region of the classical shape.

*Proof of the theorem on windows (outline).* Write $W = X^2$ and $q = Q^k$. Let $a(n) = \Lambda(n)$ if $n \equiv 1 \pmod q$ and $a(n) = 0$ otherwise. By orthogonality of characters, for $\operatorname{Re} z > 0$,
$$\sum_{n \geq 1} \frac{a(n)}{n^{1 + z}} = \frac{F(z)}{z}, \qquad F(z) = \frac{1}{\varphi(q)}\Bigl(1 - z \sum_{\chi \bmod q} \frac{(L^\ast)'}{L^\ast}(1 + z, \chi)\Bigr).$$
The term $1$ comes from the pole of $L(s, \chi_0)$. On the disc $|z| \leq 1/X$, [the lemma on zeros near $1$](/decl/New.eventually_norm_logDeriv_entireL_le_near_one/) shows that $F$ is analytic, and $|z (L^\ast)'/L^\ast| \leq 1$ for each of the $\varphi(q)$ characters, so $|F(z)| \leq 2$.

Suppose that no prime $p \equiv 1 \pmod q$ has $\log p \in [U, U + X^2]$. Let $P(z) = \sum_{n < e^U} a(n) n^{-1 - z}$, a finite sum, and
$$G(z) = \bigl(F(z) - z P(z)\bigr) \exp\Bigl(-2 + U z + \tfrac{X}{4}(1 + X z)^2\Bigr).$$
The function $G$ is analytic on the disc $|z| \leq 1/X$. At $z = 0$,
$$G(0) = F(0)\, e^{-2 + X/4} = \frac{e^{X/4 - 2}}{\varphi(q)}.$$
On the circle $|z| = 1/X$, the source proves $|G(z)| \leq 3U$. The first step is a fact about the Gaussian factor: on the circle, the real part of $-2 + Uz + \frac{X}{4}(1 + Xz)^2$ is at most $-2 + (U + u)\operatorname{Re} z$ for some $u \in [0, X^2]$. So the quadratic term acts as a shift of the cut $U$ by at most the length of the window. Then there are two cases. If $\operatorname{Re} z \leq 1/U$, the source bounds $|F(z)| \leq 2$ and the finite sum $P(z)$ term by term against the series at $1 + 1/U$, whose sum is $U F(1/U) \leq 2U$. If $\operatorname{Re} z \geq 1/U$, then $F(z) - zP(z)$ is $z$ times the tail $\sum_{n \geq e^U} a(n) n^{-1-z}$. By the hypothesis, the terms of the tail with $\log n$ in the window come from prime powers $p^j$ with $j \geq 2$ only. The series of $\Lambda$ over the numbers that are not prime converges absolutely at $3/4$, since $\psi(y) - \theta(y) = O(\sqrt{y})$, and its sum is at most $X$ for large $X$. The terms beyond the window have $\log n \geq U + X^2 \geq U + t$, and the shift makes them small. The maximum principle now gives
$$\frac{e^{X/4 - 2}}{\varphi(q)} = |G(0)| \leq \max_{|z| = 1/X} |G(z)| \leq 3U.$$
But $q \leq W^A = X^{2A}$ and $U \leq W^A = X^{2A}$, so $3 U \varphi(q) \leq 3 X^{4A} < e^{X/4 - 2}$ for large $X$. This contradiction gives a prime $p \equiv 1 \pmod q$ with $U \leq \log p \leq U + W$. $\square$

The length $W = X^2$ of the window and the radius $1/X$ of the disc are linked: a disc of radius $1/X$ resolves windows of length about $X^2$ in $\log n$. A wider zero-free region would give shorter windows. The data do not need them.

**Remark (Formalization).** The textbook result is the Siegel-Walfisz theorem in the form of Montgomery and Vaughan, Corollary 11.19. The source does not prove that theorem. It proves the special case above directly, and its file cites the corollary as the known result of which this is a consequence. The source's list of references marks this citation as compared with its source. Three points of the Lean form matter for the meaning. First, "for every large $W$" is an eventual statement along `atTop`, with no explicit threshold, so the existence theorem of Section 5 also holds only for large $x$, with no explicit bound. Second, the window is closed, $\log p \in [U, U + W]$, and $p$ is an existential witness. Third, the hypothesis $4 \mid Q$ is used only for the squares in the lemma on real characters. The application takes $Q = q_0 d$, and $4 \mid q_0$ since $18480 \mid q_0$.
