---
title: A model case
lean:
  - New/Reduction/ShortAndEnough.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## A model case

Theorem A says that certain theta lifts have coefficients that are integral, divisible at the nonsplit primes, and small at every archimedean place. This section works out the simplest theta lift with these three properties: the theta series of the norm form of an imaginary quadratic field, with a harmonic polynomial. Every step of Theorem A has a counterpart here, and the counterparts are elementary. The section uses no result of the later chapters.

### The theta series

Let $K = \mathbb{Q}(\sqrt{-7})$. Its ring of integers is $\mathcal{O}_K = \mathbb{Z}[\omega]$ with $\omega = (1 + \sqrt{-7})/2$, so $\omega^2 - \omega + 2 = 0$ and $N(x + y\omega) = x^2 + xy + 2y^2$. The class number of $K$ is $1$ and the units are $\pm 1$. The character of $K$ is the Kronecker symbol $\chi(n) = \left(\frac{-7}{n}\right)$. A prime $p \neq 7$ splits in $K$ if $p \equiv 1, 2, 4 \bmod 7$, and it is inert if $p \equiv 3, 5, 6 \bmod 7$. The prime $7$ ramifies: $7 = -(\sqrt{-7})^2$. So $2$ and $11$ split, and $3$ and $5$ are inert. The data of the argument ask for $d \equiv 7 \bmod 8$, so that $2$ splits in $K = \mathbb{Q}(\sqrt{-d})$, as it does here. The value $d = 7$ itself is too small for the data, but the model needs no sizes.

Let $j \geq 0$ be even. Put

$$\theta_j(z) = \frac12 \sum_{\alpha \in \mathcal{O}_K} \alpha^j\, q^{N\alpha} = \sum_{n \geq 0} a_j(n)\, q^n, \qquad q = e^{2\pi i z}.$$

For $j \geq 2$ the series $\theta_j$ is a cusp form of weight $j + 1$ for $\Gamma_0(7)$ with the character $\chi$. This section does not use that fact. The series $\theta_j$ is a theta lift for the norm form, with the harmonic polynomial $\alpha^j$, which fixes the archimedean type. In Theorem A the lifts go between unitary groups of large rank over $E$, and the polynomial is replaced by a Weyl module of large weight. The role of $j$ here is the role of the weights $\kappa(\sigma)$ there.

If $j$ were odd, the terms for $\alpha$ and $-\alpha$ would cancel and $\theta_j$ would be $0$. This is the first instance of a lift that can vanish identically. Theorem A has the same feature, and Section 3 discusses it.

### Integrality

**Example (Integral coefficients).** For every even $j \geq 0$ and every $n \geq 1$, the coefficient $a_j(n)$ is a rational integer.

*Proof.* Let $A_n = \{\alpha \in \mathcal{O}_K : N\alpha = n\}$. The set is finite and stable under $\alpha \mapsto -\alpha$ and under complex conjugation. As $j$ is even, $\alpha$ and $-\alpha$ give the same term $\alpha^j$, so $a_j(n)$ is the sum of $\alpha^j$ over a set of representatives of $A_n$ modulo $\pm 1$. So $a_j(n) \in \mathcal{O}_K$. Complex conjugation permutes $A_n$, so $a_j(n)$ is real. Thus $a_j(n) \in \mathcal{O}_K \cap \mathbb{R} = \mathbb{Z}$. $\square$

The integrality comes from the kernel side: the sum runs over the lattice $\mathcal{O}_K$, and the polynomial has integral coefficients. In Theorem A the integral source forms play the role of $\mathcal{O}_K$, and the theta kernels with integral vacuum data play the role of the sum over the lattice ([theta kernels and gauges](/chapter/theta-kernels-gauges/)).

### Size

Let $r_K(n) = \#A_n$. As $K$ has class number $1$ and two units, $r_K(n)$ is twice the number of ideals of norm $n$, and the number of ideals of norm $n$ is $\sum_{e \mid n} \chi(e)$. So $r_K(n) \leq 2\tau(n)$, where $\tau(n)$ is the number of divisors of $n$.

**Example (Size of the coefficients).** For every even $j$ and every $n \geq 1$,

$$|a_j(n)| \leq \tfrac12 r_K(n)\, n^{j/2} \leq \tau(n)\, n^{j/2}.$$

*Proof.* Each term has $|\alpha^j| = (N\alpha)^{j/2} = n^{j/2}$, and there are $r_K(n)$ terms. $\square$

This is the counterpart of the archimedean size. The size of a term is the size of the polynomial at the point, and the number of terms is a count of lattice points. In Theorem A the size of a kernel is governed by the jet sizes $s_\infty(\kappa) = \log \kappa! + \kappa\log(M/\Omega)$ of derivatives of order $\kappa$, and the count of terms is a class count ([the archimedean size](/chapter/archimedean-size/)).

### Divisibility

**Example (Divisibility at the nonsplit primes).** Let $j$ be even, $n \geq 1$, and let $p$ be a prime that does not split in $K$, with $v = v_p(n)$.

1. If $p$ is inert and $v$ is odd, then $a_j(n) = 0$.
2. If $p$ is inert and $v$ is even, then $p^{vj/2}$ divides $a_j(n)$.
3. If $p = 7$, then $7^{vj/2}$ divides $a_j(n)$.

*Proof.* Let $p$ be inert. Then $p\mathcal{O}_K$ is prime of norm $p^2$. If $N\alpha = n$, then the exponent $u$ of $p\mathcal{O}_K$ in $\alpha\mathcal{O}_K$ satisfies $2u = v$. If $v$ is odd, no $\alpha$ exists, so $A_n$ is empty and $a_j(n) = 0$. If $v$ is even, then $p^{v/2}$ divides every $\alpha \in A_n$, so $p^{vj/2}$ divides every term $\alpha^j$, and it divides their sum in $\mathcal{O}_K$. A rational integer divisible by $p^{vj/2}$ in $\mathcal{O}_K$ is divisible by $p^{vj/2}$ in $\mathbb{Z}$, since $\mathcal{O}_K \cap \mathbb{Q} = \mathbb{Z}$. Now let $p = 7$ and $\mathfrak{p} = \sqrt{-7}\,\mathcal{O}_K$, of norm $7$. If $N\alpha = n$, then $\mathfrak{p}^v$ divides $\alpha$, so $\mathfrak{p}^{vj}$ divides $\alpha^j$. As $j$ is even, $\mathfrak{p}^{vj} = 7^{vj/2}\mathcal{O}_K$. The same argument as before ends the proof. $\square$

Put $D_j(n) = \prod_p p^{v_p(n)\, j/2}$, the product over the primes that do not split in $K$. The example says that $D_j(n)$ divides $a_j(n)$ whenever $a_j(n) \neq 0$. At the split primes there is no divisibility of this kind: for $p = 2$, $a_2(2) = -3$ is odd.

The divisor $D_j(n)$ has a prime sum form, with the weight $\Lambda_K(\nu) = \Lambda(\nu)(1 - \chi(\nu))$ of the argument. For an inert prime $p$, $\Lambda_K(p^e)$ is $2\log p$ for odd $e$ and $0$ for even $e$. For $p = 7$, $\Lambda_K(7^e) = \log 7$. For a split prime, $\Lambda_K(p^e) = 0$. So if $v$ is even and $p$ is inert, $\sum_{e \leq v}\Lambda_K(p^e) = (v/2)\cdot 2\log p = v\log p$. For $p = 7$ the same sum is $v\log 7$. Hence, whenever $a_j(n) \neq 0$,

$$\log D_j(n) = \frac{j}{2}\sum_{\nu \mid n}\Lambda_K(\nu),$$

where $\nu$ runs over the prime powers that divide $n$. The divisibility is a prime sum with the weight $\Lambda_K$, and only the nonsplit primes contribute. This is the shape of the gain $\mathrm{gain}_p$ in Theorem A: a sum of local terms with the weight $\Lambda_K$, nonzero only at nonsplit primes.

### The balance

The three examples fit together as follows. Let $n$ have $a_j(n) \neq 0$. As $a_j(n)$ is a nonzero integer and $D_j(n)$ divides it,

$$\log D_j(n) \leq \log|a_j(n)| \leq \log\tfrac12 r_K(n) + \tfrac{j}{2}\log n.$$

The left inequality is the product formula for the nonzero rational number $a_j(n)$: the sum over all places of $\log|a_j(n)|_v$ is $0$, the finite places give at most $-\log D_j(n)$, so the archimedean place gives at least $\log D_j(n)$. The right inequality is the size bound. Write $n = n_{\mathrm{s}}\, n_{\mathrm{ns}}$, where $n_{\mathrm{ns}}$ is the part of $n$ at the nonsplit primes. Then $\log D_j(n) = \frac{j}{2}\log n_{\mathrm{ns}}$, and the gap between the two bounds is

$$\log\tfrac12 r_K(n) + \tfrac{j}{2}\log n_{\mathrm{s}}.$$

The nonsplit part of $n$ costs nothing: there the size and the divisibility are equal. At $n = p^{2e}$ for an inert $p$ the gap is $0$: $A_n = \{\pm p^e\}$, so $a_j(n) = p^{ej} = D_j(n)$. The two bounds meet.

**Example (The form $\theta_2$).** For $j = 2$ the coefficients $a_2(n)$ for $n \leq 18$ are

| $n$ | 1 | 2 | 4 | 7 | 8 | 9 | 11 | 14 | 16 | 18 |
|---|---|---|---|---|---|---|---|---|---|---|
| $a_2(n)$ | $1$ | $-3$ | $5$ | $-7$ | $-3$ | $9$ | $-6$ | $21$ | $-11$ | $-27$ |

and $a_2(n) = 0$ for the other $n \leq 18$. For instance $a_2(2) = \omega^2 + \bar\omega^2 = (\omega + \bar\omega) - 4 = -3$, since $A_2 = \{\pm\omega, \pm\bar\omega\}$. The zeros at $n = 3, 5, 6, 10, 12, 13, 15, 17$ come from part 1 of the example on divisibility: each such $n$ has an odd power of $3$ or $5$, or of the inert prime $13$ or $17$. The values $a_2(7) = -7$ and $a_2(9) = 9$ meet both bounds: $|a_2(n)| = n = D_2(n)$. The value $a_2(18) = -27$ is divisible by $D_2(18) = 9$, and $a_2(18)/9 = -3 = a_2(2)$. The value $a_2(14) = 21$ is divisible by $D_2(14) = 7$.

### Normalization

Put $b_j(n) = a_j(n)/D_j(n)$ when $a_j(n) \neq 0$. Then $b_j(n)$ is a nonzero integer, and

$$0 \leq \log|b_j(n)| \leq \log\tfrac12 r_K(n) + \tfrac{j}{2}\log n_{\mathrm{s}}.$$

Division by the divisibility removes the nonsplit part from the size, and the result is still integral. The gain factor $c_B$ of Section 4 does the same in Theorem A.

### The dictionary

| model | Theorem A |
|---|---|
| sum over $\alpha \in \mathcal{O}_K$ | theta kernels on integral vacuum data |
| harmonic polynomial $\alpha^j$ | Weyl module of weight $\kappa$ |
| $a_j(n) \in \mathbb{Z}$ | $\varphi \in \mathrm{src}_{\mathrm{int}}$, images integral |
| $\lvert a_j(n)\rvert \leq \frac12 r_K(n)\, n^{j/2}$ | archimedean size of the composite lift |
| $D_j(n) \mid a_j(n)$ | divisibility by $p^{\mathrm{gain}_p - \mathrm{err}(p)}$ |
| $\log D_j(n) = \frac{j}{2}\sum_{\nu\mid n}\Lambda_K(\nu)$ | $\mathrm{gain}_p$, a sum with the weight $\Lambda_K$ |
| $b_j(n) = a_j(n)/D_j(n)$ | multiplication by $c_B$ |
| product formula for $a_j(n)$ | lower bound of Theorem C |

Two features of Theorem A have no counterpart here. First, the model reads integrality and size from the same formula. In Theorem A the form of interest is $\Theta_1(\mathcal{P}\varphi)$, a lift of a Poincaré series, and its coefficients have no direct formula. The seesaw identity rewrites it as a composite lift of $\varphi$ itself, where the kernels act on the integral form $\varphi$ and both properties can be read off. Second, in the model the divisibility is exact at every nonsplit prime. In Theorem A it holds on a submodule of finite colength, with an error $\mathrm{err}(p)$, and the colength enters the index of part (b).
