---
title: A worked example
lean:
  - New/Reduction/Data/FieldsAndPlaces.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## A worked example

This section computes the splitting of some primes in $K$ and $E$ for the smallest parameters.

### The parameters

Take $q_0 = 18480$. A prime $d$ with $d + 1$ an odd multiple of $9240$ is a valid choice. The first candidate is $d = 9239$, and it is prime: it has no prime factor up to $\sqrt{9239} < 97$. So $(q_0, d) = (18480, 9239)$ are parameters. Check the congruences: $9239 = 1154 \cdot 8 + 7$, so $d \equiv 7 \bmod 8$, and $d \equiv 9239 = q_0/2 - 1 \bmod q_0$.

**Example (The field K).** Let $K = \mathbb{Q}(\sqrt{-9239})$. Its ring of integers is $\mathbb{Z}[\beta_K]$, with $\beta_K = (1 + \sqrt{-9239})/2$ a root of
$$X^2 - X + 2310, \qquad 2310 = \frac{9240}{4} = 2 \cdot 3 \cdot 5 \cdot 7 \cdot 11.$$
So the norm of $\beta_K$ is the product of exactly the primes below $13$. Modulo each of them the polynomial is $X(X-1)$, and the criterion of Dedekind and Kummer gives
$$p \mathcal{O}_K = (p, \beta_K)(p, \beta_K - 1), \qquad p = 2, 3, 5, 7, 11.$$
For the other primes $p \ne 9239$ we have $\chi_K(p) = (p/9239)$. A computation with Euler's criterion $(p/d) \equiv p^{(d-1)/2} \bmod d$ gives these values for the primes from $13$ to $79$.

| $\chi_K(p) = 1$ (split) | $\chi_K(p) = -1$ (inert) |
| --- | --- |
| $13, 17, 37, 43, 53, 73, 79$ | $19, 23, 29, 31, 41, 47, 59, 61, 67, 71$ |

The first inert prime is $19$. The corollary of Section 2 says only that it is at least $13$, and the class of $d$ does not fix $(13/d)$ (Exercise 2).

### The field $E$ at $s = 0$

Take $s = 0$. Then $\lfloor \log_3 0 \rfloor = 0$ by convention, $l_0(0) = 3^4 = 81$, $\mathrm{towerDeg}(0) = 3^5 = 243$, and
$$q_1 = 18480 \cdot 243 = 4490640 = 2^4 \cdot 3^6 \cdot 5 \cdot 7 \cdot 11.$$
We have $\varphi(18480) = 8 \cdot 2 \cdot 4 \cdot 6 \cdot 10 = 3840$, so the number of infinite places is
$$f = \#\Phi = 243 \cdot 3840 = 933120 = \varphi(q_1),$$
and $[E : \mathbb{Q}] = 2f = 1866240$. Of the $933120$ places, $243$ have class $1$ modulo $18480$.

The Galois group of $E$ over $\mathbb{Q}$ is $\{\pm 1\} \times (\mathbb{Z}/q_1)^\times$ (Section 3). A prime $p \nmid q_1 d$ is unramified in $E$, and its Frobenius element is
$$\mathrm{Frob}_p = (\chi_K(p),\, p \bmod q_1).$$
So the residue degree of $p$ in $E$ is the order $f_p$ of this element, the number of places of $E$ over $p$ is $2f/f_p$, and each has norm $p^{f_p}$. Complex conjugation is $c = (-1, -1)$. A place $w$ over $p$ has $\bar w = w$ if and only if $c$ lies in the decomposition group $\langle \mathrm{Frob}_p \rangle$.

**Example (Primes in E).** The orders below were computed modulo $q_1 = 4490640$.

| $p$ | $\chi_K(p)$ | $\mathrm{ord}_{q_1}(p)$ | $f_p$ | places over $p$ |
| --- | --- | --- | --- | --- |
| $13$ | $1$ | $4860$ | $4860$ | $384$ |
| $17$ | $1$ | $1620$ | $1620$ | $1152$ |
| $19$ | $-1$ | $1620$ | $1620$ | $1152$ |
| $23$ | $-1$ | $972$ | $972$ | $1920$ |
| $31$ | $-1$ | $2430$ | $2430$ | $768$ |

For $p = 31$ the order $2430$ is even, so again $f_p = \mathrm{lcm}(2, 2430) = 2430$. For split primes such as $13$ and $17$, the first coordinate of $\mathrm{Frob}_p$ is $1$, so $c \notin \langle \mathrm{Frob}_p \rangle$, and every place over $p$ is split. This must be so: $w$ lies over a prime $\mathfrak{p}$ of $K$, $\bar w$ lies over $\bar{\mathfrak{p}}$, and $\mathfrak{p} \ne \bar{\mathfrak{p}}$. For the inert primes $19, 23, 31$, a place $w$ with $\bar w = w$ needs an odd $k$ with $p^k \equiv -1 \bmod q_1$. This fails. The powers of $19$ modulo $16$ are $\{1, 3, 9, 11\}$, and the powers of $23$ modulo $16$ are $\{1, 7\}$, so neither reaches $15 \equiv -1$. For $31$ we have $31 \equiv 1 \bmod 5$, so $31^k \equiv 1 \not\equiv -1 \bmod 5$. So all places over these primes are split too.

Places with $\bar w = w$ exist, but over large primes. The prime $p = 2q_1 - 1 = 8981279$ is inert in $K$, and $p \equiv -1 \bmod q_1$. So $\mathrm{Frob}_p = (-1, -1) = c$. The places over $p$ have residue degree $2$, there are $f = 933120$ of them, and each is fixed by conjugation. Its norm is $q_w = p^2$ with $p \equiv 3 \bmod 4$, as the proposition of Section 3 predicts. The prime $q_1 - 1 = 4490639$ is also prime with $p \equiv -1 \bmod q_1$, but it splits in $K$. Its Frobenius is $(1, -1)$, of order $2$, and its places are split.

### The roots of unity

The roots of unity of $E$ are the $q_1 = 4490640$ powers of $\zeta$. The root $\zeta^{q_1 / 5040} = \zeta^{891}$ is a primitive $5040$-th root of unity, since $4490640 = 891 \cdot 5040$. The field $E$ contains no primitive $9239$-th root of unity: the field $\mathbb{Q}(\zeta_{9239}, \zeta_{q_1})$ has degree $\varphi(9239) \varphi(q_1) = 9238 \cdot 933120$, and this is larger than $[E : \mathbb{Q}] = 1866240$. This is the argument of Section 3 with $d > 64$.
