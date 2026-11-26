---
title: The prime sums
lean:
  - New/Reduction/PrimeSums.lean
  - New/Reduction/Data/AdmissibleData.lean
  - New/Reduction/Zeros/PrimeError.lean
decls:
  - New.Data.primeSum
  - New.Data.lambdaKResidueClass_mul_posPart_le_ite
  - New.Data.primeSum_le
  - New.Data.primeSum_mem_Icc
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The prime sums

This section recalls the weight $\Lambda_K$, the places and the weights $\kappa$. Then it defines the prime sum $s_{\mathrm{fin}}(y, \sigma)$ and proves that it is at most $4y \log x_1$.

### The weight $\Lambda_K$ and the remainder $R_q$

Fix the parameters $q_0$ and $d$: $q_0$ is a multiple of $18480 = 16 \cdot 3 \cdot 5 \cdot 7 \cdot 11$, and $d$ is a prime with $d \equiv q_0/2 - 1 \bmod q_0$. Then $d \equiv 7 \bmod 8$. Let $K = \mathbb{Q}(\sqrt{-d})$ and let $\chi_K(n) = (n/d)$ be the Legendre symbol, the character of $K$. For an integer $n \geq 1$ put

$$\Lambda_K(n) = \Lambda(n)\bigl(1 - \chi_K(n)\bigr),$$

where $\Lambda$ is the von Mangoldt function. For a modulus $q \geq 1$ let $\lambda_q(n) = \Lambda_K(n)$ if $n \equiv 1 \bmod q$ and $\lambda_q(n) = 0$ otherwise. So $\lambda_1 = \Lambda_K$. These are the weights of [the weighted prime remainder](/chapter/weighted-prime-remainder/). For a prime power $n = p^k$ the factor $1 - \chi_K(p^k)$ is $0$ if $p$ splits in $K$, $1$ if $p = d$ ramifies, and $1 - (-1)^k \in \{0, 2\}$ if $p$ is inert. So

$$0 \leq \Lambda_K(n) \leq 2\Lambda(n).$$

Lean: `New.lambdaKResidueClass_nonneg`, `New.lambdaKResidueClass_le_two_mul_vonMangoldt`, `New.lambdaKResidueClass_eq_ite` (New/Reduction/Zeros/PrimeError.lean, New/Reduction/PrimeSums.lean).

The remainder of that chapter is, for $z > 0$,

$$R_q(z) = \sum_{1 \leq n \leq z} \lambda_q(n)\Bigl(\frac{1}{n} - \frac{1}{z}\Bigr) - \frac{\log z}{\varphi(q)} - c_q,$$

where $c_q = \operatorname{Re} G_q(1)$ is the constant for which $R_q(z) \to 0$. For $q = 1$ the constant is explicit: $c_1 = -1 - C_d$, with $C_d = \gamma - \operatorname{Re} (L'/L)(1, \chi_K)$ (`New.chowlaSelbergConst`). The remainders that this chapter uses are $R_{q_0}$ and $R_1$. Only the shape of $R_q$ matters here, not the value of $c_q$, except for $c_1$ in Section 4.

### The places and the weights

Let $s$ be the tower exponent of the data, $q_1 = q_0 \cdot 3 l_0 2^s$ and $E = K(\zeta_{q_1})$. The infinite places of $E$ form a group $\Phi$, and $\Phi \cong \operatorname{Gal}(E/K) \cong (\mathbb{Z}/q_1\mathbb{Z})^\times$ ([fields, places and twists](/chapter/fields-places-twists/)). This chapter writes the group law of $\Phi$ as a product. For an integer $\nu$ prime to $q_1$ let $[\nu] \in \Phi$ be the place of the class of $\nu$, and for $\tau \in \Phi$ write $-\nu\tau$ for the place $[-\nu]\tau$. The number of places is

$$f = \#\Phi = \varphi(q_1) = 3 l_0 2^s \cdot \varphi(q_0).$$

The reduction modulo $q_0$ is a surjective homomorphism $\mathrm{cl} : \Phi \to (\mathbb{Z}/q_0\mathbb{Z})^\times$, the *class* of a place. The data fix two sets of places ([the data and its sizes](/chapter/data-and-sizes/)):

- $\Phi_a = \{\tau \in \Phi : \mathrm{cl}(\tau) = 1\}$, the *$a$-places*, the kernel of $\mathrm{cl}$;
- a set $\Phi_b$ of places with $\mathrm{cl}(\sigma) = -1$ for each $\sigma \in \Phi_b$, the *$b$-places*.

Since $q_0 > 2$, the classes $1$ and $-1$ differ, so $\Phi_a \cap \Phi_b = \emptyset$. The data ask that $\Phi_b$ is sparse and that $3 l_0 2^s \leq \#\Phi_b \log b$. The data also fix integer scales $x$, $x_1$, $b$ with $x^{10^6} \leq x_1$ and $x_1^{10^6} \leq b$, the long order $a = xb$, and the condition $q_1 x_1 \mid b$. The *weight* of a place is

$$\kappa(\sigma) = \begin{cases} b = a/x, & \sigma \in \Phi_b,\\ a/x_1, & \sigma \notin \Phi_b. \end{cases}$$

Since $x_1 \mid b$, both values are integers. Since $x \leq x_1$, every weight lies in $[a/x_1, a/x]$, so $\kappa(\sigma) \leq b$.

Lean: `New.Data.cast_weight`, `New.Data.weight_mem_Icc`, `New.Data.weight_le_b` (New/Reduction/Data/Magnitudes.lean, New/Reduction/Data/LevelAndTwists.lean).

### The prime sum

**Definition (Prime sum).** For a real number $y$ and a place $\sigma \in \Phi$, the *prime sum* is

$$s_{\mathrm{fin}}(y, \sigma) = \sum_{1 \leq \nu \leq a} \Lambda_K(\nu)\Bigl(\frac{y}{\nu} - \kappa(-\nu\sigma)\Bigr)_+ ,$$

where $t_+ = \max(t, 0)$.

Lean: `New.Data.primeSum` (New/Reduction/Data/AdmissibleData.lean).

The prime sum has two arguments because the argument uses it in two ways. The direction amount of Section 3 uses $s_{\mathrm{fin}}(\kappa(\sigma), \sigma)$, at every place. The total remainder of Section 4 uses $s_{\mathrm{fin}}(a, \tau)$, at the places $\tau \in \Phi_a$. Section 4 states how the two uses add up to the gains of Theorem A.

Three features of the definition matter.

1. *Only nonsplit primes count.* A prime that splits in $K$ has $\Lambda_K = 0$ at all its powers. An inert prime counts with weight $2\log p$ at odd powers and $0$ at even powers. The ramified prime $d$ counts with weight $\log d$.
2. *The weight of the term is read at the place $-\nu\sigma$, not at $\sigma$.* As $\nu$ runs over the integers prime to $q_1$, the place $-\nu\sigma$ runs over all of $\Phi$. So each $\nu$ is cut off at $y/\kappa(-\nu\sigma)$, which is $x$ or $x_1$ when $y = a$.
3. *Only $\nu \leq x_1$ contribute when $y \leq a$.* Every weight is at least $a/x_1$. If $\nu > x_1$ then $y/\nu \leq a/\nu < a/x_1 \leq \kappa$, and the positive part is $0$. The sum over $\nu \leq a$ is a finite sum that contains every term that is not $0$.

**Remark (Formalization).** The source defines $-\nu\sigma$ for every $\nu \geq 1$. It is $[-\nu]\sigma$ if $\nu$ is prime to $q_1$, and $\sigma$ itself otherwise: the place $[\nu]$ is the identity place if $\nu$ is not a unit modulo $q_1$ (`New.Parameters.placeOfInt`, [FieldsAndPlaces.lean](lean:New/Reduction/Data/FieldsAndPlaces.lean#L287)). This value has no effect on the prime sum. If $\nu = p^k$ is not prime to $q_1$, then $p \mid q_0$, and the source proves $\chi_K(p) = 1$ (`New.Parameters.chiK_eq_one_of_dvd`). So $\Lambda_K(\nu) = 0$. The identity of Section 5 does not need this fact. Its proof treats the identity place as a place of class $1$, and Section 5 checks that this is consistent.

### The bound

**Lemma (One term).** Let $0 \leq y \leq a$, let $\sigma \in \Phi$ and let $n \geq 1$. Then

$$\Lambda_K(n)\Bigl(\frac{y}{n} - \kappa(\sigma)\Bigr)_+ \leq \begin{cases} 2y\,\Lambda(n)/n, & n \leq \lfloor x_1 \rfloor,\\ 0, & n > \lfloor x_1 \rfloor. \end{cases}$$

Lean: `New.Data.lambdaKResidueClass_mul_posPart_le_ite` (New/Reduction/PrimeSums.lean).

*Proof.* Let $n \leq \lfloor x_1 \rfloor$. Since $\kappa(\sigma) \geq 0$ and $y/n \geq 0$, we have $(y/n - \kappa(\sigma))_+ \leq y/n$. With $0 \leq \Lambda_K(n) \leq 2\Lambda(n)$ the term is at most $2\Lambda(n) \cdot y/n$. Let $n > \lfloor x_1 \rfloor$. Then $n \geq x_1$, since $n$ is an integer. So $y/n \leq a/x_1 \leq \kappa(\sigma)$, and the positive part is $0$. $\square$

**Proposition (Size of the prime sum).** For $0 \leq y \leq a$ and every place $\tau \in \Phi$,

$$s_{\mathrm{fin}}(y, \tau) \leq 4y \log x_1 .$$

Lean: `New.Data.primeSum_le` (New/Reduction/PrimeSums.lean).

*Proof.* Apply the lemma to each term, at the place $\sigma = -\nu\tau$. The terms with $\nu > \lfloor x_1 \rfloor$ vanish, and $\lfloor x_1 \rfloor \leq a$. So

$$s_{\mathrm{fin}}(y, \tau) \leq 2y \sum_{1 \leq n \leq \lfloor x_1 \rfloor} \frac{\Lambda(n)}{n} \leq 2y \cdot 2 \log \lfloor x_1 \rfloor \leq 4y \log x_1 .$$

The second step is the bound $\sum_{n \leq N} \Lambda(n)/n \leq 2 \log N$ for every integer $N \geq 1$ (`New.sum_vonMangoldt_div_le`). It has a short proof. For $n \leq N$ we have $N/n < \lfloor N/n \rfloor + 1 \leq 2\lfloor N/n \rfloor$. So

$$N \sum_{n \leq N} \frac{\Lambda(n)}{n} \leq 2 \sum_{n \leq N} \Lambda(n) \Bigl\lfloor \frac{N}{n} \Bigr\rfloor = 2 \log N! \leq 2N \log N,$$

where the middle equality is $\log N! = \sum_{m \leq N} \log m = \sum_{m \leq N} \sum_{n \mid m} \Lambda(n)$. $\square$

The bound is not sharp (Exercise 6).

**Corollary.** For $0 \leq y \leq a$ and every place $\tau$,

$$0 \leq s_{\mathrm{fin}}(y, \tau) \leq y \log b .$$

Lean: `New.Data.primeSum_mem_Icc` (New/Reduction/PrimeSums.lean).

*Proof.* Each term of the prime sum is a product of $\Lambda_K(\nu) \geq 0$ and a positive part, so it is nonnegative. For the upper bound, the scale inequality $x_1^{10^6} \leq b$ gives $4 \log x_1 \leq \log b$, and the proposition applies. $\square$
