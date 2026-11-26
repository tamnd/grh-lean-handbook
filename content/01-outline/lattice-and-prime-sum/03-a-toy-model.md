---
title: A toy model
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## A toy model

This section gives a one-dimensional model of the method. A positive sum over primes is bounded by two bounds for one number. The number is an integer, so the lattice has rank one and its covolume is the number itself. The model shows three features of the source: divisibility against size, the cancellation of the main terms, and one side only. It also shows why the source needs a lattice of large rank.

### Chebyshev's bound

Let $n \geq 1$ and let
$$\vartheta(y) = \sum_{p \leq y} \log p$$
be Chebyshev's function, where $p$ runs over the primes. Consider the sum
$$S(n) = \vartheta(2n) - \vartheta(n) = \sum_{n < p \leq 2n} \log p .$$
It is a sum of positive terms. The prime number theorem says $S(n) \sim n$. The model gives an upper bound with a constant.

**Proposition (Chebyshev).** For every $n \geq 1$,
$$S(n) \leq \log \binom{2n}{n} < 2n \log 2 .$$

*Proof.* Let $B = \binom{2n}{n} = (2n)!/(n!)^2$. Each prime $p$ with $n < p \leq 2n$ divides $(2n)!$ and does not divide $n!$. So $p$ divides $B$, and the product $P = \prod_{n < p \leq 2n} p$ divides $B$. The quotient $Q = B/P$ is a positive integer, so
$$\log Q = \log B - S(n) \geq 0 .$$
This is the lower bound. The upper bound is $B < \sum_{j=0}^{2n} \binom{2n}{j} = 4^n$, the size of the number. Together, $S(n) \leq \log B < 2n\log 2$. $\square$

Read the proof as the method of the source. The number $B$ is the analogue of a Gram determinant. Its divisibility by the primes of $(n, 2n]$ is the analogue of the gains of the forms of Theorem A at the small primes. The quotient $Q = B/P$ is the analogue of the forms after the gains are divided out. The more primes there are in $(n, 2n]$, the smaller $Q$ becomes, and integrality says $Q \geq 1$. Nothing in the proof bounds $S(n)$ from below. The bound has one side, as in the source.

### Where the main terms cancel

The size bound $B < 4^n$ hides a cancellation. Legendre's formula writes a factorial as a product over primes:
$$\log N! = \sum_{\nu \leq N} \Lambda(\nu) \Bigl\lfloor \frac{N}{\nu} \Bigr\rfloor ,$$
where $\Lambda$ is the von Mangoldt function. So
$$\log B = \sum_{\nu \leq 2n} \Lambda(\nu) \Bigl( \Bigl\lfloor \frac{2n}{\nu} \Bigr\rfloor - 2 \Bigl\lfloor \frac{n}{\nu} \Bigr\rfloor \Bigr) .$$
Each bracket is $0$ or $1$, and it is $1$ for the primes $\nu = p \in (n, 2n]$. The size side is Stirling's formula, $\log N! = N \log N - N + \tfrac12 \log(2\pi N) + O(1/N)$. It gives
$$\log B = 2n \log(2n) - 2n - 2(n \log n - n) + O(\log n) = 2n \log 2 + O(\log n) .$$
The main terms $2n\log n$ of the factorials cancel, and the bound is the difference, of size $n$.

The source has the same structure. The size of a derivative of order $j$ is
$$s_\infty(j) = \log j! + j \log(M/\Omega),$$
and the divisibility that the source guarantees for it is the prime sum
$$s_{\mathrm{fin}}(y, \sigma) = \sum_{1 \leq \nu \leq a} \Lambda_K(\nu) \Bigl( \frac{y}{\nu} - \kappa(-\nu\sigma) \Bigr)^{+}, \qquad \Lambda_K(\nu) = \Lambda(\nu)(1 - \chi_K(\nu)),$$
where $\chi_K$ is the character of $K = \mathbb{Q}(\sqrt{-d})$, $\kappa$ is the weight, and $M$ and $\Omega$ are numbers of the data ([the data and its sizes](/chapter/data-and-sizes/)). The prime sum is a sum of the same kind as Legendre's sum for $\log j!$: the floor $\lfloor y/\nu \rfloor$ is replaced by the piecewise linear function $(y/\nu - \kappa)^+$, and the weight $1 - \chi_K(\nu)$ is $0$ at the primes that split in $K$ and $2$ at the primes that are inert in $K$. At the $a$-places $\tau$ and $y = a$, the expected value of $s_{\mathrm{fin}}(a, \tau)$ is
$$s_{\mathrm{main}} = a\Bigl(\log a - \frac1f \sum_{\tau} \log\kappa(\tau) + c_1\Bigr),$$
with a constant $c_1$ ([the weighted prime remainder](/chapter/weighted-prime-remainder/)). Its main term $a \log a$ is the main term of $\log a!$ in $s_\infty(a)$, by Stirling's formula. These terms cancel, as the terms $2n\log n$ cancel in the model. The rest of $s_\infty(a) - s_{\mathrm{main}}$ is about $a \log(\bar\kappa M \operatorname{rd}_E / 2\pi)$, where $\bar\kappa$ is the geometric mean of the weights and $\operatorname{rd}_E$ is the root discriminant of $E$. The source pays this rest, for all $m$ lifts together, by the level $N$ of the forms (Section 5).

### What the model cannot do

The model loses a constant factor. Chebyshev's bound gives $S(n) \leq (2\log 2)\,n \approx 1.386\,n$, while $S(n) \sim n$. The integer $B$ is fixed by $n$, and the divisibility bound does not see all of $\log B$: the exact identity $\log B = \sum \Lambda(\nu)(\lfloor 2n/\nu \rfloor - 2\lfloor n/\nu\rfloor)$ also contains the primes $\nu \in (n/2, 2n/3]$, with brackets equal to $1$, and the bound for $S(n)$ throws them away.

The source avoids the loss in three ways.

1. Exact cancellation. The main amount is the same number in the upper and the lower bound. It is not estimated on either side: it cancels as a symbol, in the last step of the proof of the main inequality. In the model, the analogous terms $2n\log n$ cancel, but the terms of size $n$ do not.
2. Many dimensions. A Gram determinant of $n$ vectors in a lattice of rank $d_T$ has $d_T$ degrees of freedom. The upper bound is a product of $n$ lengths, and the lower bound is a product over $d_T$ dimensions. When $n \geq d_T/2$, the errors per dimension, not the total errors, decide the outcome.
3. Amplification. The prime sum enters the size bound multiplied by the number $m$ of theta lifts, while the errors per dimension do not grow with $m$. In the model, the analogue would be a number of size about $B$ divisible by $P^m$. The power $B^m$ does not help, since its size is $B^m$. The chain of $m$ theta lifts of the source is the construction that does this (Section 5).

The third point gives the saving: the remainder is at most the error divided by $m$. With $m \approx \sqrt x$, this is the exponent $1/2$ of Section 6.
