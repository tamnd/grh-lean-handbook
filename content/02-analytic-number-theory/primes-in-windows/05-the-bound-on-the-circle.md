---
title: The bound on the circle
lean:
  - Lib/Analytic/Primes.lean
decls:
  - New.exists_shift_le_re_exponent
  - New.norm_le_of_term_le_majorant
  - New.norm_sub_mul_sum_term_le
  - New.analyticOnNhd_sub_mul_sum_term
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The bound on the circle

This section proves the analytic heart of the argument. Suppose that a window $[U, U + X^2]$ for $\log n$ holds no prime of the progression. Then the function $F_q(z) - zP(z)$ of Section 4, multiplied by a Gaussian factor, is at most $3U$ on the circle $|z| = 1/X$. The statements of this section are abstract: they hold for every nonnegative sequence $a$ whose Dirichlet series has the right form, and they do not mention characters. Section 6 applies them to $a = a_q$.

### Why a Gaussian factor

Fix $X \geq 200$ and $U \geq X^2$, and put
$$E(z) = 2 - Uz - \tfrac{X}{4}(1 + Xz)^2.$$
Newman's method divides by $\exp(E(z))$. The three terms of $E$ have three tasks.

1. The constant $2$ and the term $-\tfrac{X}{4}(1 + Xz)^2$ make $|\exp(-E(0))| = e^{X/4 - 2}$ large at the centre. This is the size that gives the contradiction in Section 6.
2. The term $-Uz$ moves the cut of the Dirichlet series to $n = e^U$. For $\operatorname{Re} z > 0$ the tail $\sum_{n \geq e^U} a(n)n^{-1-z}$ has terms of size $n^{-1-\operatorname{Re} z}$, and $e^{-U\operatorname{Re} z}$ is the size of $n^{-\operatorname{Re} z}$ at the cut. So $e^{U\operatorname{Re} z}$ times the tail is of moderate size.
3. On the circle, the quadratic term is not small. Its real part is $-(X^2/2)(1 + X\operatorname{Re} z)\operatorname{Re} z$, and so it acts as a further shift of the cut by a number $t \in [0, X^2]$. This is why the window has length $X^2$: the hypothesis "no prime" must hold up to $\log n = U + t$ for every point of the circle.

The next lemma makes the third point exact.

**Lemma (The shift on the circle).** Let $U \in \mathbb{R}$, let $X > 0$, and let $z \in \mathbb{C}$ with $|z| = 1/X$. Then there is $t \in \mathbb{R}$ with $0 \leq t \leq X^2$ and
$$2 - (U + t)\operatorname{Re} z \leq \operatorname{Re}\Bigl(2 - Uz - \tfrac{X}{4}(1 + Xz)^2\Bigr).$$
Lean: `New.exists_shift_le_re_exponent` (Lib/Analytic/Primes.lean).

*Proof.* Put $x = X\operatorname{Re} z$. Since $|\operatorname{Re} z| \leq |z| = 1/X$, we have $-1 \leq x \leq 1$. Since $|z|^2 = 1/X^2$, we have $X^2(\operatorname{Im} z)^2 = 1 - x^2$. Then
$$\operatorname{Re}(1 + Xz)^2 = (1 + x)^2 - X^2(\operatorname{Im} z)^2 = (1 + x)^2 - (1 - x^2) = 2x(1 + x).$$
So the real part of the exponent is
$$2 - U\operatorname{Re} z - \tfrac{X}{4}\cdot 2x(1 + x) = 2 - U\operatorname{Re} z - \tfrac{X^2}{2}(1 + x)\operatorname{Re} z = 2 - (U + t)\operatorname{Re} z$$
with $t = \tfrac{X^2}{2}(1 + x)$. Since $0 \leq 1 + x \leq 2$, we have $0 \leq t \leq X^2$. $\square$

The proof gives an equality, but the lemma states only the inequality, which is all that the next proposition uses.

**Example.** Take three points of the circle. At $z = 1/X$, we have $x = 1$ and $t = X^2$, and the exponent is $2 - U/X - X$. At $z = i/X$, we have $x = 0$ and $t = X^2/2$, and $(1 + Xz)^2 = (1 + i)^2 = 2i$, so the real part of the exponent is $2$. At $z = -1/X$, we have $x = -1$ and $t = 0$, and $(1 + Xz)^2 = 0$, so the exponent is $2 + U/X$. At the point $z = 1/X$, where the Dirichlet series decays fastest, the cut is shifted to the far end $U + X^2$ of the window. At $z = -1/X$ there is no shift, and the factor $e^{U/X}$ is large instead.

### The majorant

The second lemma turns a bound for each term into a bound for a part of the series. Its hypotheses fix the data of Newman's method. In this section $a \colon \mathbb{N} \to \mathbb{R}$ and $b \colon \mathbb{N} \to \mathbb{C}$ are sequences, $F \colon \mathbb{C} \to \mathbb{C}$ is a function, and $X, U, C$ are real numbers with the following properties.

- (H1) $a(n) \geq 0$ for every $n$.
- (H2) For every $z$ with $\operatorname{Re} z > 0$, the Dirichlet series of $a$ at $1 + z$ converges and has the sum $F(z)/z$.
- (H3) $|F(z)| \leq 2$ for $|z| \leq 1/X$.
- (H4) $\sum_n |b(n)n^{-3/4}| = C$, and $C \leq X$.
- (H5) $X \geq 200$ and $X^2 \leq U$.

Write $T_c(s, n)$ for the $n$-th term $c(n)n^{-s}$ of the Dirichlet series of $c$, with $T_c(s, 0) = 0$.

**Lemma (The majorant).** Assume (H1) to (H5). Let $z \in \mathbb{C}$, $S \in \mathbb{C}$, $E \in \mathbb{R}$, and let $s$ be a set of natural numbers. Suppose that the terms $T_a(1 + z, n)$ for $n \in s$ have the sum $S$, and that for every $n \in s$,
$$|T_a(1 + z, n)| \leq e^E\bigl(|T_a(1 + 1/U, n)| + |T_b(3/4, n)|\bigr).$$
Then $|S| \leq 3U e^E$.
Lean: `New.norm_le_of_term_le_majorant` (Lib/Analytic/Primes.lean).

*Proof.* By (H5), $X \leq X^2 \leq U$, so $U > 0$ and $1/U \leq 1/X$. By (H1) and (H2) at the real point $1/U$, the terms $|T_a(1 + 1/U, n)| = T_a(1 + 1/U, n)$ have the sum $F(1/U)/(1/U) = U F(1/U)$, which is real. By (H3), this sum is at most $2U$. Extend the bound of the hypothesis by $0$ outside $s$. The sum over all $n$ of the right side is $e^E(UF(1/U) + C) \leq e^E(2U + X) \leq 3Ue^E$, by (H4) and $X \leq U$. So $|S| \leq 3Ue^E$. $\square$

The set $s$ is a finite set in one application and an infinite set in the other. The sum over $s$ is the full majorant at $1 + 1/U$, restricted to $s$, so the lemma never needs to know which terms are in $s$.

### The main estimate

**Proposition (The bound on the circle).** Assume (H1) to (H5), and assume that $|a(n)| \leq |b(n)|$ for every $n$ with $\log n \in [U, U + X^2]$. Let $z \in \mathbb{C}$ with $|z| = 1/X$, and let
$$P(z) = \sum_{n < \lceil e^U\rceil} T_a(1 + z, n).$$
Then
$$|F(z) - zP(z)| \leq 3U\exp\Bigl(\operatorname{Re}\bigl(2 - Uz - \tfrac{X}{4}(1 + Xz)^2\bigr)\Bigr).$$
Lean: `New.norm_sub_mul_sum_term_le` (Lib/Analytic/Primes.lean).

*Proof.* Let $E$ be the real part of the exponent. By the [lemma on the shift](/decl/New.exists_shift_le_re_exponent/) there is $t \in [0, X^2]$ with $2 - (U + t)\operatorname{Re} z \leq E$. Since $t \leq X^2 \leq U$, we have $t/U \leq 1$. Also $|z| = 1/X \leq 1/200$. The [lemma on moving a term](/decl/New.norm_term_le_exp_mul/) with $\sigma = 1/U$ gives the following rule.

(R) If $\log n\,(1/U - \operatorname{Re} z) \leq E$, then $|T_a(1 + z, n)| \leq e^E|T_a(1 + 1/U, n)|$, and so the term satisfies the hypothesis of the majorant.

There are two cases.

*Case 1: $\operatorname{Re} z \leq 1/U$.* Here $\operatorname{Re} z$ may be negative, and the series of $a$ may diverge at $1 + z$. So this case uses only the finite sum $P(z)$ and the bound for $F$. Since $U\operatorname{Re} z \leq 1$ and $t\operatorname{Re} z \leq t/U \leq 1$, we have $E \geq 2 - 1 - 1 = 0$. Let $n < \lceil e^U\rceil$. Then $n < e^U$, so $\log n \leq U$ (for $n = 0$ use $\log 0 = 0 \leq U$). Since $1/U - \operatorname{Re} z \geq 0$,
$$\log n\,(1/U - \operatorname{Re} z) \leq U(1/U - \operatorname{Re} z) = 1 - U\operatorname{Re} z \leq 2 - (U + t)\operatorname{Re} z \leq E,$$
where the middle step is $t\operatorname{Re} z \leq 1$. By (R) and the [majorant](/decl/New.norm_le_of_term_le_majorant/) with the finite set $s = \{n < \lceil e^U\rceil\}$, $|P(z)| \leq 3Ue^E$. So
$$|F(z) - zP(z)| \leq 2 + \tfrac{1}{200}\cdot 3Ue^E \leq 3Ue^E,$$
since $e^E \geq 1$ and $3Ue^E \geq 3X^2 \geq 120000$.

*Case 2: $\operatorname{Re} z \geq 1/U$.* Here $\operatorname{Re} z > 0$, and by (H2) the full series converges with the sum $F(z)/z$. So $F(z)/z - P(z)$ is the sum of the terms $T_a(1 + z, n)$ over the set $s$ of $n \geq \lceil e^U\rceil$. For $n \in s$ we have $n \geq e^U$, so $\log n \geq U$. There are two kinds of $n$ in $s$.

- If $\log n \leq U + X^2$, then $n$ is in the window, and $|a(n)| \leq |b(n)|$. So $|T_a(1 + z, n)| \leq |T_b(1 + z, n)|$. Apply the lemma on moving a term to $b$ with $\sigma = -1/4$. Its hypothesis is $\log n\,(-1/4 - \operatorname{Re} z) \leq E$. Since $-1/4 - \operatorname{Re} z < 0$ and $\log n \geq U$, the left side is at most $-U/4 - U\operatorname{Re} z$. Since $t \leq U$ and $\operatorname{Re} z \leq 1/200$, we have $t\operatorname{Re} z \leq U/200$, and so $E \geq 2 - U\operatorname{Re} z - U/200$. As $-U/4 \leq -U/200 \leq 2 - U/200$, the hypothesis holds. So $|T_a(1 + z, n)| \leq e^E|T_b(3/4, n)|$.
- If $\log n \geq U + X^2$, then $\log n \geq U + t$. Since $1/U - \operatorname{Re} z \leq 0$,
$$\log n\,(1/U - \operatorname{Re} z) \leq (U + t)(1/U - \operatorname{Re} z) = 1 + t/U - (U + t)\operatorname{Re} z \leq 2 - (U + t)\operatorname{Re} z \leq E.$$
By (R), the term satisfies the hypothesis of the majorant.

In both kinds the hypothesis of the majorant holds. So $|F(z)/z - P(z)| \leq 3Ue^E$. Since $|z| \leq 1$, $|F(z) - zP(z)| = |z|\,|F(z)/z - P(z)| \leq 3Ue^E$. $\square$

The proof shows where each constant comes from. The bound $|F| \leq 2$ and the sum $C \leq X$ of the prime powers give $2U + X \leq 3U$. The radius $1/X \leq 1/200$ makes the loss $e^{t\operatorname{Re} z} \leq e^{U/200}$ in the window small against the gain $e^{-U/4}$ of the exponent $3/4$. Outside the window, the shift $t \leq X^2$ of the lemma on the shift is exactly what the length of the window covers. The hypothesis on the window is used only in the first kind of Case 2.

### Analyticity

The last lemma says that the function of the method is analytic on the closed disc, as long as no L-function vanishes there. Recall the function $F_q$ and the sequence $a_q$ of Section 4.

**Lemma (Analyticity).** Let $q \geq 1$, let $N \in \mathbb{N}$, and let $r \in \mathbb{R}$. Suppose that $L^\ast(1 + z, \chi) \neq 0$ for every $z$ with $|z| \leq r$ and every character $\chi$ modulo $q$. Then the function
$$z \mapsto \frac{1}{\varphi(q)}\Bigl(1 - z\sum_{\chi \bmod q}\frac{(L^\ast)'}{L^\ast}(1 + z, \chi)\Bigr) - z\sum_{n < N} a_q(n)n^{-1-z}$$
is analytic at every point of the closed disc $|z| \leq r$.
Lean: `New.analyticOnNhd_sub_mul_sum_term` (Lib/Analytic/Primes.lean).

*Proof.* Each $L^\ast(\cdot, \chi)$ is entire ([Dirichlet L-functions and zero symmetry](/chapter/dirichlet-l-functions/)). So its logarithmic derivative is analytic at every point where it does not vanish, and by hypothesis this includes $1 + z$ for $|z| \leq r$. Each term $a_q(n)n^{-1-z}$ is an entire function of $z$, and the sum over $n < N$ is finite. $\square$

The function $G(z) = (F_q(z) - zP(z))/\exp(E(z))$ is then analytic on the closed disc too, since $\exp$ does not vanish. Section 6 applies the maximum principle to $G$.

**Remark (Formalization).** Four points of the Lean form matter.

1. Lean's `logDeriv f` is $f'/f$ with the junk value $0$ where $f = 0$. The lemma on analyticity assumes that $L^\ast$ does not vanish on the disc, so the junk value does not occur there.
2. The finite sum is over `Finset.range ⌈rexp U⌉₊`, that is over $n < \lceil e^U\rceil$. For $U > 0$ this is the set of $n < e^U$. In Lean $\log 0 = 0$, and the term at $n = 0$ is $0$ by definition, so $n = 0$ plays no role.
3. The lemma on the majorant and the proposition are stated for abstract $a$, $b$, $F$, with (H1) to (H5) as hypotheses. The proof of the theorem in Section 6 supplies them with $a = a_q$, the $b$ of the prime powers, and $F = F_q$. The proposition asks for $|a(n)| \leq |b(n)|$ in the window, in the norm of $\mathbb{C}$, and not for $a(n) = 0$ at the primes: the primes of other classes have $a_q(n) = 0$ anyway, and the primes of the class $1$ are excluded by the hypothesis "no prime".
4. The lemma on the shift asserts only an inequality, although its proof gives the equality $\operatorname{Re} E = 2 - (U + t)\operatorname{Re} z$ with $t = (X^2/2)(1 + X\operatorname{Re} z)$.
