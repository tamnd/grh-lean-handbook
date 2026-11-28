---
title: The classical theory
lean:
  - Lib/Analytic/Primes.lean
decls:
  - New.div_add_card_le_prod_one_sub_inv
  - New.le_totient_mul_log
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The classical theory

This section collects the classical results on primes in progressions and in short intervals, and it translates each of them into the language of windows of $\log p$, which is the language of the source. The comparison shows where the theorem of the source sits: far below the theorem of Siegel and Walfisz in strength, but in a range of moduli where the classical proofs need Siegel's ineffective theorem. The section ends with a lower bound for Euler's function, which the same file of the source proves for a later use.

### Notation

Let $q \geq 1$ and let $a$ be prime to $q$. Write $\Lambda$ for the von Mangoldt function and
$$\psi(x; q, a) = \sum_{\substack{n \leq x \\ n \equiv a \ (q)}} \Lambda(n), \qquad \theta(x; q, a) = \sum_{\substack{p \leq x \\ p \equiv a \ (q)}} \log p, \qquad \pi(x; q, a) = \#\{p \leq x : p \equiv a \ (q)\}.$$
The difference $\psi(x; q, a) - \theta(x; q, a)$ is the contribution of the prime powers $p^j$ with $j \geq 2$. It is at most $\psi(x) - \theta(x) = O(\sqrt{x})$, uniformly in $q$ and $a$. A window for $\log p$ is a closed interval $[U, U + W]$ with $U, W > 0$. The prime $p$ has $\log p$ in this window if and only if $e^U \leq p \leq e^{U + W}$.

### Progressions to a fixed modulus

Dirichlet proved that every class $a$ prime to $q$ holds infinitely many primes. Davenport, *Multiplicative Number Theory*, Chapters 1 and 4, gives the proof. The key fact is $L(1, \chi) \neq 0$ for every character $\chi \neq \chi_0$ modulo $q$. The prime number theorem for progressions gives the asymptotic count.

**Theorem (The prime number theorem for progressions).** Let $q \geq 1$ be fixed. There is $c = c(q) > 0$ such that
$$\psi(x; q, a) = \frac{x}{\varphi(q)} + O_q\Bigl(x \exp\bigl(-c\sqrt{\log x}\bigr)\Bigr)$$
for all $x \geq 2$ and all $a$ prime to $q$.

Not in the source. The source proves the weaker form $|R_q(y)| \leq (\log y)^{-B}$ for fixed $q$, [Theorem](/decl/New.eventually_abs_primeRemainder_le/), and finds primes in windows by Newman's method.

This is the classical theorem of de la Vallée Poussin. Davenport, Chapter 20, proves it in a form that is uniform in $q$ and keeps one extra term for a possible exceptional zero. The chapter [the prime number theorem in progressions](/chapter/prime-number-theorem/) of this volume proves the form that the source uses for a fixed modulus. That chapter also proves the zero-free region that Section 3 uses. This chapter does not repeat its proofs.

For a fixed $q$ the theorem gives primes in every window of a fixed length. Let $W > 0$ be fixed and $x = e^U$. Then
$$\theta(xe^W; q, 1) - \theta(x; q, 1) = \frac{(e^W - 1)x}{\varphi(q)} + O_q\Bigl(xe^W\exp\bigl(-c\sqrt{U}\bigr)\Bigr),$$
and the main term wins for $U \geq U_0(q, W)$. So for a fixed modulus the windows can even shrink slowly as $U$ grows.

### Uniformity in the modulus

The data need moduli that grow. The classical proofs of uniform results meet one obstacle: a real character $\chi$ modulo $q$ can have a real zero $\beta$ of $L(s, \chi)$ very close to $1$. The classical zero-free region excludes all other zeros in a region of the form $\sigma > 1 - c/\log(q(|t| + 2))$, and it allows at most one such exceptional zero for each modulus (Davenport, Chapter 14). The theorem of Siegel bounds the exceptional zero.

**Theorem (Siegel).** For every $\eta > 0$ there is $c(\eta) > 0$ such that $L(\sigma, \chi) \neq 0$ for every real character $\chi$ modulo $q$ and every real $\sigma > 1 - c(\eta)\, q^{-\eta}$.

Not in the source. The source avoids it: for the moduli $Q^k$ every real character comes from the fixed modulus $Q^2$, [Lemma](/decl/New.factorsThrough_sq_of_sq_eq_one/).

Davenport, Chapter 21, proves it. The constant $c(\eta)$ is not effective: the proof shows that it exists, but it gives no way to compute it. Siegel's theorem gives the theorem of Siegel and Walfisz.

**Theorem (Siegel-Walfisz).** Let $A > 0$. There is a constant $c > 0$ such that
$$\psi(x; q, a) = \frac{x}{\varphi(q)} + O_A\Bigl(x \exp\bigl(-c\sqrt{\log x}\bigr)\Bigr)$$
for all $x \geq 2$, all $q \leq (\log x)^A$ and all $a$ prime to $q$. The implied constant depends on $A$ and is not effective.

Not in the source. The source cites it and proves in its place the special case [Theorem](/decl/New.exists_prime_modEq_one_log_mem/).

This is Montgomery and Vaughan, *Multiplicative Number Theory I*, Corollary 11.19, which the source cites. Davenport, Chapter 22, proves the same theorem. The chapter [the data exist](/chapter/data-exist/#primes-in-windows) of Volume 1 states it in the same form.

In the language of windows the theorem is strong. Let $x = e^U$, $q \leq U^A$ and $0 < W \leq 1$. Then $e^W - 1 \geq W$, and
$$\theta(xe^W; q, 1) - \theta(x; q, 1) \geq \frac{Wx}{U^A} - O_A\Bigl(x\exp\bigl(-c\sqrt{U}\bigr)\Bigr) - O\bigl(\sqrt{x e^W}\bigr).$$
So for $U$ large, every window of length $W \geq \exp(-\tfrac{c}{2}\sqrt{U})$ holds a prime $p \equiv 1 \pmod q$, for every $q \leq U^A$. The windows are short, but the threshold for $U$ cannot be computed.

**Remark (Without the exceptional zero).** Siegel's theorem enters only through the real characters. If for a family of moduli every real character modulo $q$ is induced from a character modulo a number of a fixed finite set, then the exceptional zeros of that family are the real zeros of finitely many fixed L-functions. None of these vanishes at $1$, so a fixed disc about $1$ has no zero of them. For such a family the proofs of the uniform theorems need no ineffective step. Section 3 shows that the moduli $Q^k$ with $4 \mid Q$ form such a family, with the fixed modulus $Q^2$.

### The least prime in a progression

Linnik proved that there are absolute constants $c$ and $\mathcal{L}$ such that every class $a$ prime to $q$ has a prime $p \equiv a \pmod q$ with $p \leq c\, q^{\mathcal{L}}$ (Linnik, *On the least prime in an arithmetic progression*, I and II, Mat. Sb. 15 (1944), 139 to 178 and 347 to 368). In the language of windows it gives one prime with $\log p \leq \mathcal{L} \log q + \log c$. That is a prime near the bottom of the scale, not a prime in a window at a prescribed height $U$. The data need primes at the heights $10 \log b$ to $24 m \log b$, far above $\log q_2^2$. So Linnik's theorem does not give the primes of the data.

### Short intervals

The theorems on primes in short intervals ask for primes in $[x, x + x^{\vartheta}]$ with $\vartheta < 1$. Hoheisel proved the first such theorem in 1930, for $\vartheta$ slightly less than $1$. Huxley proved $\pi(x + x^{\vartheta}) - \pi(x) \sim x^{\vartheta}/\log x$ for every $\vartheta > 7/12$ (Huxley, *On the difference between consecutive primes*, Invent. Math. 15 (1972), 164 to 170). Baker, Harman and Pintz proved that $[x - x^{0.525}, x]$ holds a prime for every large $x$ (*The difference between consecutive primes, II*, Proc. London Math. Soc. (3) 83 (2001), 532 to 562). On the Riemann Hypothesis, Cramér proved $p_{n+1} - p_n = O(\sqrt{p_n}\log p_n)$ (*On the order of magnitude of the difference between consecutive prime numbers*, Acta Arith. 2 (1936), 23 to 46).

In the language of windows the interval $[x, x + x^{\vartheta}]$ is a window of length about $x^{\vartheta - 1} = e^{-(1 - \vartheta)U}$ for $\log p$. These windows shrink exponentially in $U$. The windows of the source have length $W \geq U^{1/A}$ and grow with $U$. So the source does not prove, and does not need, a theorem on short intervals. Its windows are long. The word "window" in this chapter always means a window for $\log p$.

### A dictionary

The table translates each theorem into the length of the windows that it fills, for primes $p \equiv a \pmod q$ with $\log p$ near $U$.

| result | moduli | window length in $\log p$ | threshold |
|---|---|---|---|
| prime number theorem, fixed $q$ | $q$ fixed | any fixed $W > 0$ | depends on $q$, effective |
| Siegel-Walfisz | $q \leq U^A$ | $\exp(-c'\sqrt{U})$ | not effective |
| Huxley, $q = 1$ | $q = 1$ | $e^{-(5/12 - \delta)U}$ | effective |
| Linnik | all $q$ | one prime with $\log p \leq \mathcal{L}\log q + O(1)$ | effective |
| the source (Section 6) | $q = Q^k \leq W^A$, $4 \mid Q$, $k \geq 2$ | $W$, for $W \leq U \leq W^A$ | exists, not computed |

The last row is the theorem of the source. For $q = Q^k$ in the Siegel-Walfisz range it fills windows of length $W \geq U^{1/A}$, a power of $U$. The Siegel-Walfisz theorem fills windows of length $\exp(-c'\sqrt{U})$, with $c' = c/2$. In this sense the source form is very weak. Its one gain is the proof: it needs no exceptional zero bound, so no step of it is ineffective in principle.

On GRH, the explicit formula gives $\psi(x; q, a) = x/\varphi(q) + O(\sqrt{x}\log^2(qx))$, uniformly in $q \leq x$. This book does not assume GRH, since GRH is the claim that the source sets out to prove. The bound is mentioned only to show the scale of the problem.

### A lower bound for Euler's function

The file of the source that proves the theorem on windows also proves a lower bound for $\varphi(n)$. It plays no role in the proof of that theorem, where only the trivial bound $\varphi(q) \leq q$ is used. The classical result is sharp.

**Theorem (Landau).** $\displaystyle\liminf_{n \to \infty} \frac{\varphi(n) \log\log n}{n} = e^{-\gamma}$, where $\gamma$ is Euler's constant.

Not in the source. The source proves only the weaker bound with explicit constants for every $n$, [Lemma](/decl/New.le_totient_mul_log/).

This is Hardy and Wright, *An Introduction to the Theory of Numbers*, Theorem 328. It gives $n/\varphi(n) \leq (e^{\gamma} + o(1))\log\log n$. The source needs only a weak bound with a logarithm, but with explicit constants and for every $n$. It comes from a lemma on products.

**Lemma (Products over a finite set).** Let $S$ be a finite set of natural numbers, and let $a \in \mathbb{N}$ with $a < p$ for every $p \in S$. Then
$$\frac{a}{a + \#S} \leq \prod_{p \in S}\Bigl(1 - \frac{1}{p}\Bigr)$$
in $\mathbb{Q}$.
Lean: `New.div_add_card_le_prod_one_sub_inv` (Lib/Analytic/Primes.lean).

*Proof.* By induction on $\#S$. For $S = \emptyset$ the left side is $a/a$, which is $1$ for $a > 0$ and $0/0 = 0$ for $a = 0$; in both cases it is at most $1$. Otherwise let $b$ be the least element of $S$, and put $S' = S \setminus \{b\}$. Every element of $S'$ exceeds $b$, so the hypothesis of induction, with $b$ in place of $a$, gives $b/(b + \#S') \leq \prod_{p \in S'}(1 - 1/p)$. Since $b \geq a + 1$, and $t \mapsto t/(t + c)$ increases for $c > 0$,
$$\frac{a}{a + \#S' + 1} \leq \frac{b - 1}{b + \#S'} = \Bigl(1 - \frac{1}{b}\Bigr)\frac{b}{b + \#S'} \leq \Bigl(1 - \frac{1}{b}\Bigr)\prod_{p \in S'}\Bigl(1 - \frac{1}{p}\Bigr).$$
The last step uses $1 - 1/b \geq 0$. $\square$

The lemma does not ask the elements of $S$ to be prime. The bound is sharp for $S = \{a + 1, \dots, a + j\}$, since the product telescopes: $\prod_{i=1}^{j}(1 - 1/(a + i)) = a/(a + j)$.

**Lemma (Euler's function).** For every integer $n \geq 1$,
$$n \leq \varphi(n)\,(2\log n + 1).$$
Lean: `New.le_totient_mul_log` (Lib/Analytic/Primes.lean).

*Proof.* Let $j$ be the number of distinct prime factors of $n$. Each is at least $2$, and their product divides $n$, so $2^j \leq n$ and $j \log 2 \leq \log n$. The formula $\varphi(n) = n\prod_{p \mid n}(1 - 1/p)$ and the [lemma on products](/decl/New.div_add_card_le_prod_one_sub_inv/) with $a = 1$ give $\varphi(n) \geq n/(1 + j)$, so $n \leq \varphi(n)(1 + j)$. Finally $1 + j \leq 1 + \log n/\log 2 \leq 1 + 2\log n$, since $1/\log 2 < 1.45 < 2$. $\square$

**Example.** For $n = 2$ the bound reads $2 \leq 1 \cdot (2\log 2 + 1) \approx 2.39$. For $n = 30030 = 2 \cdot 3 \cdot 5 \cdot 7 \cdot 11 \cdot 13$ it reads $30030 \leq 5760 \cdot 21.62 \approx 124{,}500$, while $n/\varphi(n) \approx 5.21$. The bound loses a factor of about $\log n/\log\log n$ against the theorem of Landau, and no constant is hidden.

**Remark (Formalization).** The source uses the lemma on Euler's function in the volume on Theorem B, in the file `New/Spanning/MainTerm/BadTypes.lean`, with $n = t^r - 1$, where $t$ is the number of elements of a finite field. There it gives a lower bound for the number of primitive polynomials of degree $r$ over that field. The classical theorems of this section (Dirichlet, de la Vallée Poussin, Siegel, Siegel and Walfisz, Linnik, Huxley) have no Lean form in the source. The source cites Montgomery and Vaughan, Corollary 11.19, as the known result of which its theorem on windows is a consequence, and its list of references marks this citation as compared with its source. The source does not prove that corollary. It proves the weaker theorem of Section 6 by another method. Findings F-066 and F-102 of the [register of findings](/chapter/register-of-findings/) record this.
