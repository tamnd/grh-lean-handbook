---
title: How the argument picks its primes
lean:
  - Lib/Analytic/Primes.lean
  - New/Reduction/Data/Existence.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## How the argument picks its primes

This chapter gives the background and the full proof of one theorem of the source: for a fixed $Q$ with $4 \mid Q$ and a fixed exponent $A$, every long window of $\log p$ holds a prime $p \equiv 1 \pmod{Q^k}$, uniformly in $k$ as long as $Q^k$ is at most a power of the length of the window. The argument uses this theorem only once, to pick the three primes of the data. The chapter first gives the classical theory of primes in short intervals and in progressions. Then it proves the theorem of the source with every constant that the source fixes, and it compares the two.

### The three primes of the data

[The data and its sizes](/chapter/data-and-sizes/) in Volume 1 lists the fields of the data $D$, and [the data exist](/chapter/data-exist/) builds them at every large integer $x$. This chapter keeps the notation of that chapter. The parameters $P$ fix a multiple $q_0$ of $18480$ and a prime $d$, and $K = \mathbb{Q}(\sqrt{-d})$. At the length $x$ the recipe of the source fixes $\varepsilon$ with $0 < \varepsilon < 1/100$, the scale $W = x^{\varepsilon/6}$, the exponent $s = 22(e + 1)$ with $2^s = m^{22}$ and $s \leq 32 \log x$, and the scale $b$ with $\log b \in [W^6, W^6 + 1]$. The modulus of the primes is
$$q_2^2 = (q_0 d)^{2(s + 6)}.$$
The data need three primes $\equiv 1 \pmod{q_2^2}$.

1. The two *level primes* $p_0 \neq p_1$ of the principal level $M = p_0 p_1$. The field `levelPrime_mem` of the admissible data says that $b^{10} \leq p_i \leq b^{11}$ for $i = 0, 1$. The data also need an integer $\alpha$ of $K$ with $\alpha\bar\alpha = p_0 p_1$.
2. The prime $N$, the level of the forms. Its logarithm must lie in $[\log N_-, \log N_- + \sqrt{\log b}]$, where $\log N_-$ is an explicit number between $m \log b$ and $24 m \log b$. The data also need an integer $\beta$ of $E$ with $\beta\bar\beta = N$.

Lean: `New.Parameters.IsAdmissibleData.levelPrime_mem` (New/Reduction/Data/Existence.lean).

The source finds all three primes in windows of one length $W$ in the scale $\log p$. Put $L = \log b$. The table gives the windows. The class number of $K$ is $h$.

| prime | window for $\log p$ | start $U$ | used for |
|---|---|---|---|
| $p_0, p_1$ | $[U_i, U_i + W]$, $0 \leq i \leq h$ | $U_i = 10L + 2iW$ | `levelPrime_mem` and $\alpha\bar\alpha = p_0 p_1$ |
| $N$ | $[U, U + W]$ | $U = \log N_- \in [mL, 24mL]$ | $\log N \in [\log N_-, \log N_- + \sqrt{L}]$ |

For $p_0$ and $p_1$ the source takes $h + 1$ disjoint windows inside $[10L, 11L]$. This gives $h + 1$ distinct primes, and a pigeonhole argument in the class group of $K$ picks two of them whose product is a norm ([the lemma on two primes with a norm](/decl/New.Parameters.exists_prime_pair_norm/)). For $N$ one window is enough ([the lemma on the prime N](/decl/New.Parameters.exists_prime_log_mem_Icc_mul_star_eq/)). Every start $U$ of the table lies in $[L, 24mL]$, and [the existence of admissible data](/decl/New.Parameters.IsLargeScale.exists_isAdmissibleData/) shows that $[L, 24mL] \subseteq [W, W^{n + 7}]$ and $q_2^2 \leq W^{n + 7}$, where $n$ is the fixed exponent of [the large scales](/decl/New.Parameters.IsLargeScale/).

### What the data ask of the primes

The modulus $q_2^2$ grows with $x$. Its logarithm is $2(s + 6)\log(q_0 d)$, which is of the order of $\log x$. So the modulus is a power of $x$, and a power of $W$. A theorem for a fixed modulus does not give these primes. The data ask for a prime in a progression whose modulus is polynomial in the length of the window. In the scale $p$ itself the windows are very long: the window $[U, U + W]$ for $\log p$ is the interval $[e^U, e^{U}e^{W}]$ for $p$, and the ratio $e^W$ of its ends is huge. The data never ask for a prime in a short interval in the usual sense.

Three features of the data make the task easier than the theorem of Siegel and Walfisz.

1. Only the residue class $1$ is needed.
2. The moduli are powers $Q^k$ of one number $Q = q_0 d$, and $4 \mid Q$, since $4 \mid 18480 \mid q_0$.
3. One prime in each window is enough. No count of primes is needed.

The second feature is the key one. A real character modulo $Q^k$ comes from the fixed modulus $Q^2$ (Section 3). So the moduli of the data have no exceptional zeros, and the ineffective theorem of Siegel is not needed.

### A small example

Take $Q = 4$ and $k = 2$, so that the modulus is $16$. The primes $p \equiv 1 \pmod{16}$ below $500$ are $17$, $97$, $113$, $193$, $241$, $257$, $337$, $353$, $401$, $433$ and $449$. Take $W = U = 3$. The window $[3, 6]$ for $\log p$ is the interval $[e^3, e^6] \approx [20.1, 403.4]$ for $p$. It holds $97$, since $\log 97 \approx 4.57$, and seven more of these primes. The theorem of the source holds only for large $W$, and its threshold is enormous (Section 6), so this example only shows the shape of the statement. It does show one feature of the windows. Here $\varphi(16) = 8$, and the expected number of primes $p \equiv 1 \pmod{16}$ in $[e^3, e^6]$ is about $(e^6 - e^3)/(8 \log e^{4.5}) \approx 10.6$ by the prime number theorem for progressions. A window of length $W$ in $\log p$ holds many primes as soon as $e^W$ is large against $\varphi(q)\, U$.

### The plan of the chapter

The proof of the source has three steps.

1. **An algebraic step.** If $4 \mid Q$ and $k \geq 2$, every unit $u \equiv 1 \pmod{Q^2}$ is a square modulo $Q^k$. So every character $\chi$ modulo $Q^k$ with $\chi^2 = 1$ is induced from a character modulo $Q^2$, and has the same L-function.
2. **A disc without zeros.** By the zero-free region of [the prime number theorem in progressions](/chapter/prime-number-theorem/), for every large $X$, no $L(s, \chi)$ with $\chi$ modulo $Q^k \leq X^A$ vanishes on the disc $|s - 1| \leq 1/X$, and its logarithmic derivative is at most $X$ there. The real characters are handled by step 1 and by continuity at $s = 1$.
3. **Newman's contour argument.** Suppose that the window $[U, U + X^2]$ holds no prime $p \equiv 1 \pmod{Q^k}$. Then an analytic function on the disc $|z| \leq 1/X$ is at most $3U$ on the boundary circle, but at least $e^{X/4 - 2}/\varphi(Q^k)$ at the centre. For large $X$ this is false.

The window length is $W = X^2$. The radius $1/X$ of the disc and the length $X^2$ of the window are linked. A disc of radius $1/X$ without zeros resolves the primes only in windows of length about $X^2$ in $\log p$.

The sections follow the order in which a reader needs the results. Section 2 gives the classical theory: the prime number theorem in progressions, the theorems of Siegel and Walfisz and of Linnik, the theorems on primes in short intervals, and a dictionary that translates each of them into windows of $\log p$. It ends with a lower bound for Euler's function that the same file of the source proves. Section 3 proves steps 1 and 2. Section 4 sets up Newman's method: a model case, the generating function of the primes $\equiv 1 \pmod q$, and the series of the prime powers. Section 5 proves the bound on the circle. Section 6 proves the theorem, lists its thresholds, applies it to the three primes of the data, and compares it with the theorem of Siegel and Walfisz. Section 7 has the exercises and the notes.

This chapter uses the L-functions $L(s, \chi)$, their continuation and the non-vanishing on $\operatorname{Re} s \geq 1$ from [Dirichlet L-functions and zero symmetry](/chapter/dirichlet-l-functions/), and the zero-free region from [the prime number theorem in progressions](/chapter/prime-number-theorem/). It does not prove these facts again. It does not use [polar functions](/chapter/polar-functions/) or [Landau's theorem](/chapter/landau-theorem/). The theorem on windows does not depend on GRH or on any hypothesis on zeros. Lean accepts the theorem if the checks that the source reports hold. This book did not rerun the checks.
