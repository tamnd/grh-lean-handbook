---
title: The expected value and the total remainder
lean:
  - New/Reduction/PrimeSums.lean
  - New/UpperBound/Size/ArchimedeanSize.lean
decls:
  - New.Data.mainPrimeSum
  - New.Data.totalRemainder
  - New.Data.jetSize_sub_mainPrimeSum_le
  - New.Data.mul_jetSize_sub_mainPrimeSum_sub_le
  - New.Data.two_mul_sum_gain_mul_log
  - New.Data.mainAmount_sub_add_two_mul_sum_gain
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The expected value and the total remainder

The total remainder is the sum, over the $a$-places $\tau$, of the prime sum $s_{\mathrm{fin}}(a, \tau)$ minus an expected value $s_{\mathrm{main}}$. This section finds $s_{\mathrm{main}}$ by a heuristic, gives the two definitions, and states how the lattice argument uses them.

### Mertens' theorem with the weight $\Lambda_K$

For $q = 1$ and $z > 0$ write

$$S_1(z) = \sum_{n \leq z} \Lambda_K(n)\Bigl(\frac{1}{n} - \frac{1}{z}\Bigr).$$

The definition of the remainder in [the weighted prime remainder](/chapter/weighted-prime-remainder/) is

$$S_1(z) = \log z + c_1 + R_1(z), \qquad c_1 = \operatorname{Re} G_1(1) = -1 - C_d,$$

where $C_d = \gamma - \operatorname{Re}(L'/L)(1, \chi_K)$.

Lean: `New.re_logDerivMean_one` (New/Reduction/Zeros/PrimeError.lean).

This defines $R_1(z)$. The content is that $\log z + c_1$ is the right main term. Split $\Lambda_K = \Lambda - \Lambda\chi_K$. Mertens' theorem in the sharp form $\sum_{n \leq z}\Lambda(n)/n = \log z - \gamma + o(1)$ and the prime number theorem $\sum_{n \leq z}\Lambda(n) = z + o(z)$ give

$$\sum_{n \leq z}\Lambda(n)\Bigl(\frac1n - \frac1z\Bigr) = \log z - \gamma - 1 + o(1).$$

The prime number theorem for $L(s, \chi_K)$ gives $\sum_{n \leq z}\chi_K(n)\Lambda(n)/n \to -(L'/L)(1, \chi_K)$ and $\sum_{n \leq z}\chi_K(n)\Lambda(n) = o(z)$. Subtract. The result is $S_1(z) = \log z - 1 - C_d + o(1)$, so $R_1(z) \to 0$ as $z \to \infty$. This chapter does not use $R_1(z) \to 0$.

### The heuristic for $s_{\mathrm{main}}$

Fix a place $\tau$ and look at

$$s_{\mathrm{fin}}(a, \tau) = \sum_{1 \leq \nu \leq a}\Lambda_K(\nu)\Bigl(\frac{a}{\nu} - \kappa(-\nu\tau)\Bigr)_+ .$$

Suppose first that the weight $\kappa(-\nu\tau)$ is a constant $a/z$, independent of $\nu$, with $z \leq a$. Then the observation "a weight is a cut-off" of Section 1 gives $s_{\mathrm{fin}}(a, \tau) = a\, S_1(z) = a(\log z + c_1 + R_1(z))$, and $\log z = \log(a/\kappa)$. So the main term would be $a(\log(a/\kappa) + c_1)$.

The weight is not constant. The place $-\nu\tau$ moves with $\nu$. If the places $-\nu\tau$ were equidistributed in $\Phi$ as $\nu$ runs over the primes, then the right value of $\log(a/\kappa)$ would be its mean over all $f$ places. Write

$$\log\bar\kappa = \frac{1}{f}\sum_{\sigma \in \Phi}\log\kappa(\sigma)$$

for the mean of $\log \kappa$. Then $\bar\kappa$ is the geometric mean of the weights, and the heuristic main term is

$$s_{\mathrm{main}} = a\Bigl(\log\frac{a}{\bar\kappa} + c_1\Bigr) = a\Bigl(\log a - \frac{1}{f}\sum_{\sigma \in \Phi}\log\kappa(\sigma) + c_1\Bigr).$$

The heuristic has a gap. The map $\nu \mapsto -\nu\tau$ depends on $\nu$ modulo $q_1$. The weight $a/x$ cuts the terms off at $\nu < x$, and $q_1 \geq x^{11}$. So each class modulo $q_1$ contains at most one $\nu \leq x$, and the places $-\nu\tau$ with $\nu \leq x$ are not equidistributed. Section 5 avoids this. It sums over $\tau \in \Phi_a$ first, and after that sum only the class of $\nu$ modulo $q_0$ matters. The result is that the heuristic is exact for the mean over $\Phi_a$: the main terms of $\sum_{\tau \in \Phi_a}s_{\mathrm{fin}}(a, \tau)$ are exactly $\#\Phi_a \cdot s_{\mathrm{main}}$.

Here is a check of this, before the proof. The weights take two values: $a/x$ on $\Phi_b$ and $a/x_1$ on the other places. So

$$\log\frac{a}{\bar\kappa} = \frac{\#\Phi_b}{f}\log x + \Bigl(1 - \frac{\#\Phi_b}{f}\Bigr)\log x_1 = \log x_1 + \frac{\#\Phi_b}{f}(\log x - \log x_1).$$

The fraction $\#\Phi_b / f$ is the proportion of places with the short length $x$. Section 5 finds the main term $\log x_1 + c_1 + (\#\Phi_b/(\#\Phi_a\varphi(q_0)))(\log x - \log x_1)$ for each $a$-place, and $f = \#\Phi_a\varphi(q_0)$. The two agree.

### The two definitions

**Definition (Expected value).** The *expected value* of the prime sums at the $a$-places is

$$s_{\mathrm{main}} = a\Bigl(\log a - \frac{1}{f}\sum_{\tau \in \Phi}\log\kappa(\tau) + c_1\Bigr), \qquad c_1 = \operatorname{Re} G_1(1).$$

Lean: `New.Data.mainPrimeSum` (New/Reduction/PrimeSums.lean).

**Definition (Total remainder).** The *total remainder* is

$$\mathrm{rem} = \sum_{\tau \in \Phi_a}\bigl(s_{\mathrm{fin}}(a, \tau) - s_{\mathrm{main}}\bigr).$$

Lean: `New.Data.totalRemainder` (New/Reduction/PrimeSums.lean).

**Remark (Formalization).** The source writes $c_1$ as `(logDerivMean P.d 1 1).re`, the real part of $G_1(1)$ for the modulus $1$. It does not write $-1 - C_d$. The lemma `New.re_logDerivMean_one` gives $\operatorname{Re} G_1(1) = -1 - C_d$, and Volume 9 uses it to cancel $c_1$ against the period $\Omega$. The division by $f$ is a real division with $f > 0$, so there is no junk value. Each weight is a natural number with $\kappa(\tau) \geq a/x_1 \geq 1$, so each $\log\kappa(\tau)$ is the true logarithm. The sum in $\mathrm{rem}$ runs over $\Phi_a$ only, not over all places. The reason is in the next subsection.

### How the lattice argument uses the two definitions

The rest of this section states forward results from [the archimedean size](/chapter/archimedean-size/) (Volume 9). They explain why the expected value has this form, and why the sum runs over $\Phi_a$. This chapter does not use them.

In Theorem A, a chain of $m$ theta lifts is asked to be divisible by $p^{\mathrm{gain}_p}$ at each small prime $p < x_1$ that does not split in $K$. The gains add up to the prime sums.

**Proposition (Gains and prime sums).** Let $U$ be the set of primes $p < x_1$ with $\chi_K(p) \neq 1$. Then

$$2\sum_{p \in U}\mathrm{gain}_p \log p = m\sum_{\tau \in \Phi_a}s_{\mathrm{fin}}(a, \tau) + m k\sum_{\tau \in \Phi}s_{\mathrm{fin}}\bigl(\kappa(\tau), \tau\bigr).$$

Lean: `New.Data.two_mul_sum_gain_mul_log` (New/UpperBound/Size/ArchimedeanSize.lean).

The two sums on the right have two sources. Each lift has a Young diagram at each place $\tau$. Its first row has main length $a$ at the $a$-places and $0$ at the other places, and its next $k - 1$ rows have main length $\kappa(\tau)$ (Lean: `New.Data.rowMainLength`). The prime sums $s_{\mathrm{fin}}(a, \tau)$ come from the first rows, so they occur only at the $a$-places. The prime sums $s_{\mathrm{fin}}(\kappa(\tau), \tau)$ come from the rows of length $\kappa(\tau)$. The second kind is already in the main amount. The first kind is in $m \cdot \mathrm{rem}$, after the subtraction of $m\, \#\Phi_a\, s_{\mathrm{main}}$.

**Proposition (The exponent).**

$$\mathrm{main} - m\cdot\mathrm{rem} + 2\sum_{p \in U}\mathrm{gain}_p\log p = m\, \#\Phi_a\, s_{\mathrm{main}} + m k\sum_{\tau \in \Phi}s_\infty\bigl(\kappa(\tau)\bigr).$$

Lean: `New.Data.mainAmount_sub_add_two_mul_sum_gain` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* Insert the proposition on gains, the definitions of the main amount, the direction amount and $\mathrm{rem}$. All prime sums cancel. $\square$

So the right side has no prime sums. The next proposition compares $s_{\mathrm{main}}$ with the jet size $s_\infty(a)$ of a first row.

**Proposition (Excess of one lift).** Let $w = f^{-1}\sum_{\tau \in \Phi}\log\kappa(\tau)$ and $G = \log(M\,\mathrm{rd}_E/2\pi)$. Then

$$s_\infty(a) - s_{\mathrm{main}} \leq a(w + G) + 1 + \frac{\log a}{2}.$$

Lean: `New.Data.jetSize_sub_mainPrimeSum_le` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* Stirling's formula in the form of an upper bound gives $\log a! \leq a\log a - a + 1 + \tfrac12\log a$ for $a \geq 1$. The source takes this from the fact that $\log$ of the Stirling sequence $n!/(\sqrt{2n}(n/e)^n)$ decreases, so it is at most its value $1 - \tfrac12\log 2$ at $n = 1$. The period is $\Omega = e^{C_d}\cdot 2\pi/\mathrm{rd}_E$, so

$$\log\frac{M}{\Omega} = -C_d + \log\frac{M\,\mathrm{rd}_E}{2\pi} = 1 + c_1 + G,$$

since $c_1 = -1 - C_d$. So

$$s_\infty(a) - s_{\mathrm{main}} = \log a! + a(1 + c_1 + G) - a(\log a - w + c_1) \leq a(w + G) + 1 + \tfrac12\log a .$$

The terms $a\log a$, $a$ and $a c_1$ cancel. $\square$

This is the reason for the constant $c_1$ in $s_{\mathrm{main}}$ and for the factor $e^{C_d}$ in $\Omega$: the two constants cancel. The level $N$ is chosen to absorb the rest $a(w + G)$.

**Proposition (The level absorbs the excess).** $m\bigl(s_\infty(a) - s_{\mathrm{main}}\bigr) - a\log N \leq 32\, a\log b$.

Lean: `New.Data.mul_jetSize_sub_mainPrimeSum_sub_le` (New/UpperBound/Size/ArchimedeanSize.lean).

The proof uses the choice of the prime $N$: the data give $\log N \geq m w + (m - 1)G - \tfrac{15}{2}\log b$ (Lean: `New.Data.log_N_mem_Icc_logLevelTarget`). With the excess of one lift, the terms $m a(w + G)$ cancel, and the rest $m(1 + \tfrac12\log a) + a(G + \tfrac{15}{2}\log b)$ is at most $32 a\log b$, since $|G| \leq 23\log b$ (Lean: `New.Data.abs_log_M_mul_rootDisc_le`).

In short, each first row of length $a$ costs $s_\infty(a)$ in size and gains $s_{\mathrm{fin}}(a, \tau)$ in divisibility. The expected gain $s_{\mathrm{main}}$ and the level pay for the cost up to $32 a\log b$. What is left of the gain is the total remainder. The main inequality says that this rest, times $m$, is at most $f a (\log b)^5$.
