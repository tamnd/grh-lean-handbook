---
title: The bound at x
lean:
  - New/Reduction/OneSidedBound.lean
  - New/Reduction/PrimeSums.lean
decls:
  - New.Data.primeRemainder_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The bound at x

The main inequality bounds the total remainder $\mathrm{rem}$. The total remainder is a sum over the $a$-places of prime sums less their expected values. This section turns the bound for $\mathrm{rem}$ into a bound for one number, the weighted prime remainder $R_{q_0}(x)$ at the length $x$ of the data. The step is an exact identity and one division.

### The statement of the bound

**Theorem (The bound at $x$).** Let $P$ be parameters, with modulus $q_0$ and prime $d$, and let $D$ be admissible data for $P$. Write $R_q = R_q^{(d)}$ for the weighted prime remainder with the character $\chi_K = (\cdot/d)$. Then

$$R_{q_0}(x) \;\leq\; \frac{\varphi(q_0) \log^6 b}{m} + |R_{q_0}(x_1)| + \log b \cdot |R_1(x_1)|.$$

Lean: `New.Data.primeRemainder_le` (New/Reduction/OneSidedBound.lean).

The right side has three terms. The first is the term of the method: the main inequality, divided by $m$. The other two are the remainders at the second cut-off $x_1$. Section 5 shows that they are smaller than every power of $x$. So the first term decides the size of the bound.

### The idea of the bound

The identity for the total remainder (Section 2) reads

$$\mathrm{rem} \;=\; a \Big( \#\Phi_b \big( R_{q_0}(x) - R_{q_0}(x_1) \big) + \#\Phi_a \, R_1(x_1) \Big).$$

It comes from the choice of the weights. At the $b$-places the weight is $a/x$, so the prime sum at a $b$-place has length $x$. At the other places the weight is $a/x_1$, and the prime sum has length $x_1$. In the sum over the $a$-places $\tau$, the term of $n$ looks at the place $(-n)\tau$. The number of $a$-places $\tau$ with $(-n)\tau \in \Phi_b$ is $\#\Phi_b$ if $n \equiv 1 \pmod{q_0}$, and $0$ otherwise (`New.Data.card_filter_mem_bPlaces`). So the primes $n \equiv 1 \pmod{q_0}$ up to $x$ appear $\#\Phi_b$ times, and all primes up to $x_1$ appear $\#\Phi_a$ times. This gives the combination above. [The prime sums and the total remainder](/chapter/prime-sums/) proves the identity.

Solve the identity for $R_{q_0}(x)$:

$$R_{q_0}(x) \;=\; \frac{\mathrm{rem}}{a \, \#\Phi_b} + R_{q_0}(x_1) - \frac{\#\Phi_a}{\#\Phi_b} R_1(x_1). \tag{4.1}$$

The first term is at most $f a \log^5 b / (m a \#\Phi_b)$ by the main inequality. Since $f = \varphi(q_0) \#\Phi_a$, this is $\varphi(q_0) (\#\Phi_a / \#\Phi_b) \log^5 b / m$. The ratio $\#\Phi_a / \#\Phi_b$ is at most $\log b$ by (2.1). This gives the first term of the theorem. The other two terms of (4.1) are bounded by their absolute values.

### The proof of the bound

*Proof.* The proof uses five facts about the data.

1. $m > 0$, $a > 0$ and $\log b > 0$. These follow from the sizes of the data.
2. $\#\Phi_a = \operatorname{towerDeg}(s) > 0$.
3. $\#\Phi_a \leq \#\Phi_b \log b$. This is the condition $\operatorname{towerDeg}(s) \leq \#\Phi_b \log b$ of the data, with fact 2.
4. $f = \#\Phi_a \cdot \varphi(q_0)$.
5. The identity for the total remainder.

From facts 2 and 3, $\#\Phi_b \log b > 0$, so $\#\Phi_b > 0$, and $\#\Phi_a / \#\Phi_b \leq \log b$.

Divide [the main inequality](/decl/New.star_inequality/) by $m > 0$:

$$\mathrm{rem} \;\leq\; \frac{f a \log^5 b}{m}. \tag{4.2}$$

By fact 5, and since $a \#\Phi_b > 0$, the equation (4.1) holds. Apply (4.2) to the first term of (4.1). Bound $R_{q_0}(x_1)$ by $|R_{q_0}(x_1)|$. The third term is $-(\#\Phi_a/\#\Phi_b) R_1(x_1)$, and since $\#\Phi_a / \#\Phi_b \geq 0$, it is at most $(\#\Phi_a/\#\Phi_b) |R_1(x_1)|$. This gives

$$R_{q_0}(x) \;\leq\; \frac{f a \log^5 b}{m \, a \, \#\Phi_b} + |R_{q_0}(x_1)| + \frac{\#\Phi_a}{\#\Phi_b} |R_1(x_1)|.$$

By fact 4, the first term is $\varphi(q_0) \cdot (\#\Phi_a/\#\Phi_b) \log^5 b / m$. Replace $\#\Phi_a/\#\Phi_b$ by $\log b$ in both places where it occurs. Both coefficients are nonnegative, so the bound stays true. $\square$

**Remark.** The total remainder may be negative. Then the first term of (4.1) is negative, and the bound is true with room. The method gives no lower bound for $R_{q_0}(x)$, and the criterion needs none.

**Remark.** The factor $a$ cancels. The main inequality has $a = xb$ on the right, and the identity has $a$ in front of the bracket. So the length $b$ of the long order, which is far larger than $x$, does not appear in the bound at $x$ except through $\log b$.

**Remark (Formalization).** The source proves the bound by a chain of four steps (`calc`). The first step rewrites $R_{q_0}(x)$ with the identity `New.Data.totalRemainder_eq` and clears the denominators. The source writes $|R_{q_0}(x_1)|$ and $|R_1(x_1)|$ with absolute values because the prime number theorem of Section 5 bounds the absolute values. The fact $\#\Phi_a = \operatorname{towerDeg}(s)$ is `New.Data.card_aPlaces`, the condition on $\Phi_b$ is the field `New.Data.towerDeg_le_card_bPlaces_mul`, and $f = \#\Phi_a \varphi(q_0)$ is `New.Data.f_eq_card_aPlaces_mul`.

### The sizes of the three terms

Section 6 inserts the sizes $m \geq \sqrt{x}$, $\log b \leq 2x^\varepsilon$ and $\log x_1 \geq x^{\varepsilon/12}$. Then the first term is at most $64 \varphi(q_0) x^{-1/2 + 6\varepsilon}$, and Section 5 makes the other two at most $x^{-2}(1 + 2x^\varepsilon)$. No zero-free region near the line $\operatorname{Re} s = 1/2$ is used for the terms at $x_1$.

### Example

Take $q_0 = 18480$, so $\varphi(q_0) = \varphi(2^4) \varphi(3) \varphi(5) \varphi(7) \varphi(11) = 8 \cdot 2 \cdot 4 \cdot 6 \cdot 10 = 3840$. Suppose that the data have $x = 10^{2000}$, $\varepsilon = 1/200$ and $\log b = x^{\varepsilon} = 10^{10}$, and suppose that $m = 2^{3322}$, the least power of $2$ above $\sqrt{x} = 10^{1000}$. (These numbers show the orders of size only. The data have more conditions, for example $\log \log b \geq 10^{12} C_P$, and the data of Section 6 exist only for large $x$.) Then

$$\frac{\varphi(q_0) \log^6 b}{m} \;\leq\; \frac{3840 \cdot 10^{60}}{10^{1000}} \;<\; 10^{-936}.$$

The bound is $x^{-1/2}$ times a factor $3840 \cdot 10^{60}$, which is less than $x^{0.04}$. The saving $x^{-1/2}$ comes from $m$ alone. The loss $x^{6\varepsilon}$ comes from $\log^6 b$.
