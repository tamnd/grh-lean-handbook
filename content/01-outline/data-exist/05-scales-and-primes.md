---
title: The scales and the primes
lean:
  - New/Reduction/Data/Existence.lean
decls:
  - New.Parameters.IsLargeScale
  - New.Parameters.exists_eventually_isLargeScale
  - New.exists_isLeast_two_pow_three_pow
  - New.exists_isLeast_dvd_log_log_mem_Icc
  - New.Parameters.exists_prime_pair_norm
  - New.Parameters.exists_prime_log_mem_Icc_mul_star_eq
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The scales and the primes

This section collects the inequalities that the recipe needs into one definition, the *large scale*, and proves that $W = x^{\varepsilon/6}$ is a large scale for $y = \log x$ at every large $x$. It then builds the ranks, the scales $x_1$ and $b$, and the three primes from a large scale and from windows for primes. Section 6 puts the pieces together. The sizes are those of [the data and its sizes](/chapter/data-and-sizes/).

### Large scales

**Definition (Large scale).** Let $P$ be parameters, $n \in \mathbb{N}$ and $y, W \in \mathbb{R}$. Let $h$ be the class number of $K = \mathbb{Q}(\sqrt{-d})$, and let $c_P$ be the constant of the parameters (see below). Then $W$ is a *large scale for $y$ with exponent $n$* if the following nine conditions hold:

1. $100\,(6 \log W + 1) \leq y$;
2. $10^{12}\, c_P \leq \log W$;
3. $2 \cdot 10^6\, y \leq W$;
4. $2h + 2 \leq W$;
5. $0 < n$;
6. $n + 1 \leq W$;
7. $99\, q_0\, d\, y \leq n \log W$;
8. $(5184\, y)^n \leq W$;
9. $7776\, y\, n\, 2^n \leq W$.

Lean: `New.Parameters.IsLargeScale` (New/Reduction/Data/Existence.lean).

The constant $c_P$ is the sum of a bound for the conjugates of the integral vacuum, the number $2d + 6$, $q_0$, the absolute value of the constant $\gamma - \operatorname{Re} L'/L(1, \chi_K)$, and $\sum_w |\log |\Phi'(w)||$, where $\Phi$ is the cyclotomic polynomial of order $q_0$ and $w$ runs over its roots. It depends on $q_0$ and $d$ only. The chapter [the data and its sizes](/chapter/data-and-sizes/) explains where each part is used.

The conditions say that $W$ is small against $x = e^y$ (condition 1), large against the parameters (conditions 2 and 4), and large against every fixed power of $y$ that the construction meets (conditions 3, 8 and 9). Condition 7 is the reason for the exponent $n$: it makes the modulus $q_2^2$ at most $W^n$. Conditions 8 and 9 are the hypotheses $(5184 y)^n \leq W$ and $7776 y n 2^n \leq W$ of [the sparse set from the ranks](/decl/New.Parameters.exists_isSparse_of_ranks/).

**Lemma (A large scale exists).** Let $0 < \varepsilon < 1/100$. There is an $n \in \mathbb{N}$ such that, for every large integer $x$, $W = x^{\varepsilon/6}$ is a large scale for $y = \log x$ with exponent $n$.
Lean: `New.Parameters.exists_eventually_isLargeScale` (New/Reduction/Data/Existence.lean).

*Proof.* Choose $n > 0$ with $n \cdot \varepsilon/6 > 99\, q_0 d$. Then $\log W = (\varepsilon/6) \log x$, so $n \log W \geq 99\, q_0 d \log x$ for $x \geq 1$, which is condition 7. Condition 1 reads $100(\varepsilon \log x + 1) \leq \log x$, that is $(1 - 100\varepsilon)\log x \geq 100$. It holds for large $x$, because $\varepsilon < 1/100$. Conditions 3, 8 and 9 have the form $C (\log x)^j \leq x^{\varepsilon/6}$ with $C$ and $j$ fixed once $n$ is fixed, and $(\log x)^j = o(x^{\varepsilon/6})$. Conditions 2, 4 and 6 hold for large $x$, since $W \to \infty$. $\square$

Here the order of the quantifiers matters. The exponent $n$ is chosen first, from $\varepsilon$, $q_0$ and $d$. Then the threshold for $x$ depends on $n$, through $(5184 y)^n \leq W$ and $7776 y n 2^n \leq W$. The constant $5184^n$ is huge, so the threshold is huge, but it is a fixed number.

At a large scale the source derives some consequences, used below. If $s \leq 32 y$, then $q_2^2 \leq W^n$, since $\log q_2^2 = 2(s + 6)\log(q_0 d) \leq 99\, q_0 d\, y \leq n \log W$ for $y \geq 2$, with the crude bound $\log(q_0 d) \leq q_0 d$. As $q_1 d$ and $2^s$ divide $q_2^2$, also $q_1 d \leq W^n$ and $2^s \leq W^n$. And $W \geq 1$ and $y \geq 100$ hold at every large scale.

### The ranks

**Lemma (The ranks).** Let $y \geq 2$. There are $m, r, s \in \mathbb{N}$ with the following properties.

1. $m$ is the least power of $2$ with $m \geq e^{y/2}$, and $m \leq 2 e^{y/2}$.
2. $r$ is the least power of $3$ with $r \geq e^{5y}$, and $r \leq 3e^{5y}$.
3. $m = 2^{e + 1}$ and $s = 22(e + 1)$ for some $e \in \mathbb{N}$, and $r = 3^{e' + 1}$ for some $e' \in \mathbb{N}$.
4. $s \leq 32\, y$.

Lean: `New.exists_isLeast_two_pow_three_pow` (New/Reduction/Data/Existence.lean).

*Proof.* For $q > 1$ and $z > 1$ the least power of $q$ that is at least $z$ is $q^{e + 1}$ with $q^e < z$. The exponent is positive since $z > 1$. Then $q^{e + 1} < q z$, which gives the upper bounds. For $s$: $2^e < e^{y/2}$ gives $e \log 2 < y/2$, so $s = 22(e + 1) < 11 y/\log 2 + 22 \leq 32 y$, as $11/\log 2 < 15.9$ and $22 \leq 11 y$. $\square$

With $y = \log x$ the lemma gives $m \in [\sqrt{x}, 2\sqrt{x}]$, $r \in [x^5, 3x^5]$, $2^s = m^{22}$ and $s \leq 32 \log x$. These are the fields of the ranks in [the data and its sizes](/chapter/data-and-sizes/).

### The scales $x_1$ and $b$

The scale $x_1$ is $\lfloor e^W \rfloor$. For $W \geq 0$ its logarithm lies in $[W - 1, W]$: the upper bound is $\lfloor e^W \rfloor \leq e^W$, and the lower bound follows from $e^W < \lfloor e^W \rfloor + 1 \leq 2\lfloor e^W \rfloor \leq e \lfloor e^W \rfloor$.

**Lemma (The scale $b$).** Let $q, n \in \mathbb{N}$ and $W \in \mathbb{R}$ with $0 < q$, $1 \leq W$, $n + 1 \leq W$ and $q \leq W^n$. Let $x_1 = \lfloor e^W \rfloor$. There is a least $b \in \mathbb{N}$ with $q x_1 \mid b$ and $e^{W^6} < b$. It satisfies
$$W^6 \leq \log b \leq W^6 + 1 \qquad\text{and}\qquad 6 \log W \leq \log\log b \leq 6 \log W + 1.$$
Lean: `New.exists_isLeast_dvd_log_log_mem_Icc` (New/Reduction/Data/Existence.lean).

*Proof.* Put $c = q x_1$. Then $c \leq W^n e^W \leq e^{nW} e^W = e^{(n + 1)W} \leq e^{W^2} \leq e^{W^6}$, using $W \leq e^W$, $n + 1 \leq W$ and $W \geq 1$. The least multiple of $c$ above $e^{U}$, $U = W^6$, is $b = c(\lfloor e^U/c \rfloor + 1)$. It satisfies $e^U < b \leq e^U + c \leq 2 e^U \leq e^{U + 1}$, so $\log b \in [U, U + 1]$. For the double logarithm, $\log\log b \geq \log W^6 = 6 \log W$, and $\log b \leq W^6 + 1 \leq e \cdot W^6$ gives $\log\log b \leq 6\log W + 1$. $\square$

The application takes $q = q_1$. At a large scale and for $s \leq 32 y$, $q_1 \leq q_1 d \leq W^n$, so the lemma applies.

The divisibility $q_1 x_1 \mid b$ is a field of the data. The definition of $b$ as a least element is what [the existence theorem](/decl/New.eventually_exists_data/) states, so a reader can compute $b$ from $x$.

### The primes $p_0$ and $p_1$

The data need two distinct primes $p_0, p_1 \equiv 1 \pmod{q_2^2}$ in $[b^{10}, b^{11}]$ whose product is a norm from $K$. A single prime $p \equiv 1 \pmod{q_1 d}$ splits in $K$, but its prime factors need not be principal. A pigeonhole argument in the class group gives a pair whose product is principal.

**Lemma (Two primes with a norm).** Let $s \in \mathbb{N}$ and $W, L \in \mathbb{R}$ with $0 < W$ and $(2h + 2) W \leq L$, where $h$ is the class number of $K$. Assume that for every $U \in [10L, 11L]$ there is a prime $p \equiv 1 \pmod{q_2^2}$ with $\log p \in [U, U + W]$. Put $b = e^L$. There are primes $p_0 \neq p_1$ and an integer $\alpha$ of $K$ such that, for $i = 0, 1$, $p_i \equiv 1 \pmod{q_2^2}$ and $p_i \in [b^{10}, b^{11}]$, and
$$\alpha\bar\alpha = p_0 p_1.$$
Lean: `New.Parameters.exists_prime_pair_norm` (New/Reduction/Data/Existence.lean).

*Proof.* For $i = 0, 1, \dots, h$ take the window that starts at $U_i = 10L + 2iW$. Since $2iW + W \leq (2h + 1) W \leq L$, the window $[U_i, U_i + W]$ lies in $[10L, 11L]$, and the hypothesis gives a prime $p_i \equiv 1 \pmod{q_2^2}$ in it. Then $p_i \in [b^{10}, b^{11}]$. The windows are disjoint, since $U_i + W < U_{i + 1}$, so the $h + 1$ primes are distinct.

Each $p_i$ is $\equiv 1$ modulo $q_1 d$, which divides $q_2$. In particular $p_i \equiv 1 \pmod d$, so the character $\chi_K$ of $K$ has $\chi_K(p_i) = 1$, and $p_i$ splits: $(p_i) = I_i J_i$ with prime ideals $I_i$, $J_i$ of norm $p_i$. There are $h + 1$ ideals $I_0, \dots, I_h$ and $h$ ideal classes. So two of them, $I_i$ and $I_j$ with $i \neq j$, have the same class. Since $I_j J_j = (p_j)$ is principal, the class of $J_j$ is the inverse of the class of $I_j$, which is the inverse of the class of $I_i$. So $I_i J_j$ is principal, say $I_i J_j = (\alpha)$. Then $\alpha\bar\alpha$ is the norm of $(\alpha)$, which is $N(I_i)N(J_j) = p_i p_j$. Take $p_0 = p_i$ and $p_1 = p_j$. $\square$

The pigeonhole step is a general fact: given $h + 1$ pairs $(I_i, J_i)$ of prime ideals with each $I_i J_i$ principal, some $I_i J_j$ with $i \neq j$ is principal. The condition $(2h + 2)W \leq L$ is where condition 4 of a large scale enters: $(2h + 2) W \leq W^2 \leq \log b$.

### The prime $N$

The level $N$ must be a prime $\equiv 1 \pmod{q_2^2}$ with $\log N$ in an interval of length $\sqrt{\log b}$ that starts at $\log N_-$. Here
$$\log N_- = m \cdot \frac{1}{\#\Phi}\sum_{\tau \in \Phi} \log \kappa(\tau) + (m - 1) \log \frac{M\, \mathrm{rd}_E}{2\pi} - \frac{15}{2} \log b,$$
with the weights $\kappa$, the product $M = p_0 p_1$ and the root discriminant $\mathrm{rd}_E$ of $E$. The chapter [the data and its sizes](/chapter/data-and-sizes/) proves that $m \log b \leq \log N_- \leq 24 m \log b$ when $\log b \geq 7$, $m \geq 2$, the weights lie in $[1, b]$, $M \in [b^{20}, b^{22}]$ and $q_1 d \leq b$.

**Lemma (The prime $N$).** Let $s, m, M \in \mathbb{N}$, let $\kappa \colon \Phi \to \mathbb{N}$, and let $W, L \in \mathbb{R}$ with $2 \leq m$, $7 \leq L$, $W^2 \leq L$, $\kappa(\tau) \in [1, e^L]$ for every $\tau$, $M \in [e^{20L}, e^{22L}]$ and $q_1 d \leq e^L$. Assume that for every $U \in [mL, 24mL]$ there is a prime $p \equiv 1 \pmod{q_2^2}$ with $\log p \in [U, U + W]$. Then there are a prime $N \equiv 1 \pmod{q_2^2}$ and an integer $\beta$ of $E$ with
$$\log N_- \leq \log N \leq \log N_- + \sqrt{L} \qquad\text{and}\qquad \beta\bar\beta = N,$$
where $\log N_-$ is formed with $s$, $m$, $\kappa$, $M$ and $L = \log b$.
Lean: `New.Parameters.exists_prime_log_mem_Icc_mul_star_eq` (New/Reduction/Data/Existence.lean).

*Proof.* By the bounds for $\log N_-$, the point $U = \log N_-$ lies in $[mL, 24mL]$. The hypothesis gives a prime $N \equiv 1 \pmod{q_2^2}$ with $\log N_- \leq \log N \leq \log N_- + W \leq \log N_- + \sqrt{L}$. Since $4 \mid q_0$ and $q_0 \mid q_1 d \mid q_2^2$, $N \equiv 1 \pmod 4$. By Fermat's theorem on sums of two squares, $N = a^2 + b'^2$ with integers $a, b'$. The field $E$ contains $\zeta_{q_1}$ and $4 \mid q_1$, so it contains $i$, with $\bar\imath = -i$. Put $\beta = a + b' i$. Then $\beta\bar\beta = a^2 + b'^2 = N$. $\square$

The last step shows that a prime $N \equiv 1 \pmod 4$ is $\beta\bar\beta$ for some integer $\beta$ of $E$. This is the cheapest way to find an element of norm $N$ in the sense of the data. The data ask for $\beta\bar\beta = N$ in $E$, not for a prime of $E$ of norm $N$ over $\mathbb{Q}$. The element $a + b'i$ already lies in $\mathbb{Q}(i) \subseteq E$.

**Remark (Formalization).** Four points. First, the primes $p_i$ and the ideals $I_i$, $J_i$ are chosen with `choose`, and the pair $(i, j)$ is an existential witness of the pigeonhole step. The data record only the properties, so no later step depends on the choice. Second, the prime $N$ is found in one window of length $W$, which is shorter than the interval of length $\sqrt{\log b}$ that the data allow. The source uses $W \leq \sqrt{L}$ to pass from one to the other. Third, the weights enter only through $\log N_-$ and through the bounds $\kappa(\tau) \in [1, b]$. The weight off $\Phi_b$ is $\lfloor x b / x_1 \rfloor$, a natural-number quotient. It lies in $[1, b]$ when $1 \leq x \leq x_1 \leq b$, by `New.ite_mul_div_mem_Icc`: the quotient is at least $1$ since $xb \geq b \geq x_1$, and at most $b$ since $xb \leq x_1 b$. Fourth, some small steps of this section have their own names in the source: `New.Parameters.constantBound` is $c_P$; `New.log_floor_exp_mem_Icc` is the bound $\log x_1 \in [W - 1, W]$; `New.Parameters.IsLargeScale.exists_isLeast_dvd_log_log_mem_Icc` applies the lemma on $b$ with $q = q_1$ and also records $e^{\log b} = b$; `New.exists_ne_isPrincipal_mul` is the pigeonhole step; and `New.Parameters.exists_mul_star_eq_prime` is the sum of two squares.
