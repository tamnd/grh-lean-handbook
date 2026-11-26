---
title: A small case, and the use of the identity
lean:
  - New/Reduction/PrimeSums.lean
  - New/Reduction/MainInequality.lean
  - New/Reduction/OneSidedBound.lean
decls:
  - New.star_inequality
  - New.Data.primeRemainder_le
  - New.eventually_primeRemainder_natCast_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## A small case, and the use of the identity

This section checks the identity in a case with four places. Then it deduces the one-sided bound for $R_{q_0}(x)$.

### A small case

The real data are far too large to compute with: $q_0$ is a multiple of $18480$, and $\log\log b \geq 10^{12}$. The proof of Section 5 uses only the following properties of the data, so a small case with these properties is a fair test:

1. $\Phi$ is a group $(\mathbb{Z}/q_1\mathbb{Z})^\times$ with $q_0 \mid q_1$, and every prime factor of $q_1$ divides $q_0$;
2. $\Phi_a$ is the kernel of the reduction modulo $q_0$, and every place of $\Phi_b$ has class $-1$;
3. $1 \neq -1$ modulo $q_0$;
4. the weight is $a/x$ on $\Phi_b$ and $a/x_1$ elsewhere, both natural numbers, with $0 < x \leq x_1 \leq a$.

The case below has these properties. It does not satisfy the other conditions of the data. For example, it has $q_0 = 4$, and it does not have $q_1 x_1 \mid b$. The proof of Section 5 uses only $x_1 \mid a$ from that condition.

**Example (Four places).** Take $q_0 = 4$, $q_1 = 8$ and $d = 7$, so $K = \mathbb{Q}(\sqrt{-7})$ and $\chi_K(n) = (n/7)$. The group of places is $\Phi = (\mathbb{Z}/8\mathbb{Z})^\times = \{1, 3, 5, 7\}$, with $f = 4$ and $\varphi(q_0) = 2$. The classes modulo $4$ are $1, -1, 1, -1$. So $\Phi_a = \{1, 5\}$, and $\#\Phi_a = 2 = q_1/q_0$. Take $\Phi_b = \{7\}$. Take $x = 6$, $x_1 = 12$ and $b = 12$, so $a = xb = 72$. The weights are $\kappa(7) = 12 = a/x$ and $\kappa(1) = \kappa(3) = \kappa(5) = 6 = a/x_1$.

*The weight $\Lambda_K$.* The terms $\nu > x_1 = 12$ contribute $0$, since $72/\nu < 6 \leq \kappa$. The squares modulo $7$ are $1, 2, 4$. So for the prime powers $\nu \leq 12$:

| $\nu$ | 2 | 3 | 4 | 5 | 7 | 8 | 9 | 11 |
|---|---|---|---|---|---|---|---|---|
| $(\nu/7)$ | $1$ | $-1$ | $1$ | $-1$ | $0$ | $1$ | $1$ | $1$ |
| $\Lambda_K(\nu)$ | $0$ | $2\log 3$ | $0$ | $2\log 5$ | $\log 7$ | $0$ | $0$ | $0$ |

The prime $2$ splits in $K$, as Section 2 says for the primes that divide $q_0$. The prime $7$ ramifies, and $\Lambda_K(7) = \log 7$.

*The left side.* The prime sum at $\tau$ is $s_{\mathrm{fin}}(72, \tau) = \sum_\nu\Lambda_K(\nu)(72/\nu - \kappa([-\nu]\tau))_+$. Modulo $8$, $-3 \equiv 5$, $-5 \equiv 3$ and $-7 \equiv 1$.

| $\tau$ | $\nu$ | $[-\nu]\tau$ | $\kappa$ | $(72/\nu - \kappa)_+$ |
|---|---|---|---|---|
| $1$ | $3$ | $5$ | $6$ | $18$ |
| $1$ | $5$ | $3$ | $6$ | $42/5$ |
| $1$ | $7$ | $1$ | $6$ | $30/7$ |
| $5$ | $3$ | $1$ | $6$ | $18$ |
| $5$ | $5$ | $7$ | $12$ | $12/5$ |
| $5$ | $7$ | $5$ | $6$ | $30/7$ |

Only one pair meets $\Phi_b$: $\tau = 5$ and $\nu = 5$. This matches the count of Section 5: $\nu = 5 \equiv 1 \pmod 4$ meets $\#\Phi_b = 1$ place of $\Phi_b$, and $\nu = 3$ and $\nu = 7$, which are $\equiv 3 \pmod 4$, meet none. So

$$\sum_{\tau \in \Phi_a}s_{\mathrm{fin}}(72, \tau) = 36\cdot 2\log 3 + \frac{54}{5}\cdot 2\log 5 + \frac{60}{7}\log 7 = 72\log 3 + \frac{108}{5}\log 5 + \frac{60}{7}\log 7 .$$

*The remainder terms.* Write $S_q(z) = \sum_{n \leq z}\lambda_q(n)(1/n - 1/z)$ for the sum without the constants, so $R_q(z) = S_q(z) - \log z/\varphi(q) - c_q$. The prime powers $n \equiv 1 \pmod 4$ up to $12$ are $5$ and $9$, and $\Lambda_K(9) = 0$. So

$$S_{4}(6) = 2\log 5\Bigl(\frac15 - \frac16\Bigr) = \frac{\log 5}{15}, \qquad S_{4}(12) = 2\log 5\Bigl(\frac15 - \frac1{12}\Bigr) = \frac{7\log 5}{30},$$

$$S_1(12) = 2\log 3\Bigl(\frac13 - \frac1{12}\Bigr) + \frac{7\log 5}{30} + \log 7\Bigl(\frac17 - \frac1{12}\Bigr) = \frac{\log 3}{2} + \frac{7\log 5}{30} + \frac{5\log 7}{84}.$$

The part of the proposition on the sum over $\Phi_a$ without constants is

$$a\Bigl(\#\Phi_b\bigl(S_4(6) - S_4(12)\bigr) + \#\Phi_a S_1(12)\Bigr) = 72\Bigl(-\frac{\log 5}{6} + \log 3 + \frac{7\log 5}{15} + \frac{5\log 7}{42}\Bigr).$$

This is $72\log 3 + \frac{108}{5}\log 5 + \frac{60}{7}\log 7$, the left side.

*The main terms.* The logarithms of the weights are $\log 6$ at three places and $\log 12$ at one. The lemma on the sum of the logarithms gives $f(\log a - \log x_1) - \#\Phi_b(\log x - \log x_1) = 4\log 6 + \log 2 = 3\log 6 + \log 12$, which is right. Then, with $\log 72 = \log 6 + \log 12$,

$$\#\Phi_a\, s_{\mathrm{main}} = 2\cdot 72\Bigl(\log 72 - \frac{3\log 6 + \log 12}{4} + c_1\Bigr) = 144\Bigl(\log 12 - \frac{\log 2}{4} + c_1\Bigr).$$

The main terms of the proposition are $a(\#\Phi_a(\log x_1 + c_1) + \#\Phi_b(\log x - \log x_1)/\varphi(q_0)) = 72(2\log 12 + 2c_1 - \tfrac12\log 2)$. This is the same number. The constants $c_4$ cancel in $R_4(6) - R_4(12)$, and $c_1$ cancels between $R_1(12)$ and $s_{\mathrm{main}}$. So $\mathrm{rem} = a(\#\Phi_b(R_4(6) - R_4(12)) + \#\Phi_a R_1(12))$ in this case, for every value of $c_1$ and $c_4$.

### The use: the one-sided bound

The main inequality is the end of the lattice argument. This chapter takes it as given.

**Theorem (Main inequality).** For admissible data $D$, $m\cdot\mathrm{rem} \leq f a(\log b)^5$.

Lean: `New.star_inequality` (New/Reduction/MainInequality.lean).

The proof is in [the main inequality and the end of the proof](/chapter/main-inequality/). With the identity, it becomes a bound for $R_{q_0}(x)$.

**Corollary (The bound for $R_{q_0}(x)$).** For admissible data $D$,

$$R_{q_0}(x) \leq \frac{\varphi(q_0)(\log b)^6}{m} + |R_{q_0}(x_1)| + \log b\cdot|R_1(x_1)|.$$

Lean: `New.Data.primeRemainder_le` (New/Reduction/OneSidedBound.lean).

*Proof.* The numbers $m$, $a$, $\#\Phi_a$ and $\log b$ are positive. The data give $\#\Phi_a = 3 l_0 2^s \leq \#\Phi_b\log b$, so $\#\Phi_b > 0$ and $\#\Phi_a/\#\Phi_b \leq \log b$. Divide the identity by $a\,\#\Phi_b$:

$$R_{q_0}(x) = \frac{\mathrm{rem}}{a\,\#\Phi_b} + R_{q_0}(x_1) - \frac{\#\Phi_a}{\#\Phi_b}R_1(x_1).$$

The main inequality gives $\mathrm{rem} \leq f a(\log b)^5/m$, and $f = \varphi(q_0)\,\#\Phi_a$. So the first term is at most

$$\frac{\varphi(q_0)\,\#\Phi_a(\log b)^5}{m\,\#\Phi_b} \leq \frac{\varphi(q_0)(\log b)^6}{m}.$$

Bound $R_{q_0}(x_1) \leq |R_{q_0}(x_1)|$ and $-(\#\Phi_a/\#\Phi_b)R_1(x_1) \leq \log b\cdot|R_1(x_1)|$. $\square$

Section 3 used the condition $3 l_0 2^s \leq \#\Phi_b \log b$ to bound the direction amount. Here it bounds $\#\Phi_a/\#\Phi_b$ by $\log b$.

The first term is $x^{-1/2}$ times a power of $\log b$, since $m \geq \sqrt{x}$. The other two are errors of the prime number theorem at the second scale $x_1$. The data can be chosen with $\log b \leq 2x^\varepsilon$ and $\log x_1 \geq x^{\varepsilon/12}$ (Lean: `New.eventually_exists_data_scales`). Then the prime number theorem for the fixed moduli $q_0$ and $1$ makes $|R_{q_0}(x_1)|$ and $|R_1(x_1)|$ at most $x^{-2}$.

**Theorem (One-sided bound at integers).** Let $0 < \varepsilon < 1/100$. For all large integers $x$,

$$R_{q_0}(x) \leq \bigl(64\,\varphi(q_0) + 3\bigr)\,x^{-1/2 + 6\varepsilon}.$$

Lean: `New.eventually_primeRemainder_natCast_le` (New/Reduction/OneSidedBound.lean).

The proof is in [the main inequality and the end of the proof](/chapter/main-inequality/). It inserts the scales into the corollary: $(\log b)^6/m \leq 64\,x^{6\varepsilon}\,x^{-1/2}$, and the two errors at $x_1$ are at most $x^{-2}$ and $2x^{\varepsilon}x^{-2}$. [Landau's criterion](/chapter/landau-criterion/) then turns the bound into the absence of zeros in $\operatorname{Re} s > 1/2 + 6\varepsilon$.

The exponent $-1/2$ comes from the factor $1/m$ and the size $m \geq \sqrt{x}$ of the data. Every other factor in the first term is a power of $\log b$, so it costs only $x^{O(\varepsilon)}$. The identity loses nothing, since it is exact. So the exponent is decided by $m$ and by the main inequality alone.
