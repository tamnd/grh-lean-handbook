---
title: Exercises
lean:
  - Lib/Analytic/Primes.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $Q > 1$ be odd and let $k \geq 2$. Show that every unit $u \equiv 1 \pmod Q$ is a square modulo $Q^k$. Deduce that every character $\chi$ modulo $Q^k$ with $\chi^2 = 1$ is induced from a character modulo $Q$. Compare with the case $4 \mid Q$ of Section 3, where the modulus $Q^2$ is needed in place of $Q$.

*Hint.* Since $2$ is a unit modulo $Q^k$, Newton's iteration $x \mapsto x - (x^2 - u)/(2x)$, started at $x = 1$, doubles the exponent of $Q$ in $x^2 - u$ at each step. A real character is trivial on the squares.

**Exercise 2.** Let $Q = 12$ and $k \geq 2$. Show that there are exactly $8$ characters $\chi$ modulo $12^k$ with $\chi^2 = 1$, and that their conductors are $1, 3, 4, 8, 8, 12, 24, 24$. Check that each of them is induced from a character modulo $Q^2 = 144$, as the [lemma on squares](/decl/New.factorsThrough_sq_of_sq_eq_one/) asserts.

*Hint.* $(\mathbb{Z}/12^k)^\times \cong (\mathbb{Z}/3^k)^\times \times (\mathbb{Z}/2^{2k})^\times$. The first factor is cyclic of even order, and the second is $\{\pm 1\}$ times a cyclic group of order $2^{2k - 2}$. Use the four real characters modulo powers of $2$ from the model case of Section 3.

**Exercise 3.** Let $X > 0$ and $z = (1 + i)/(\sqrt{2}X)$. Compute $\operatorname{Re}\bigl(2 - Uz - \tfrac{X}{4}(1 + Xz)^2\bigr)$ directly, and check that it equals $2 - (U + t)\operatorname{Re} z$ with $t = \tfrac{X^2}{2}(1 + X\operatorname{Re} z)$, as in the proof of the [lemma on the shift](/decl/New.exists_shift_le_re_exponent/).

*Hint.* $Xz = (1 + i)/\sqrt{2}$, so $(1 + Xz)^2 = 1 + \sqrt{2}(1 + i) + i$. Both sides equal $2 - U/(\sqrt{2}X) - \tfrac{X}{4}(1 + \sqrt{2})$.

**Exercise 4.** Let $b(n) = \Lambda(n)$ for $n$ not prime and $b(n) = 0$ for $n$ prime. Show that
$$\sum_{n \geq 1}\frac{b(n)}{n^{3/4}} = \sum_p\frac{\log p}{p^{3/2} - p^{3/4}},$$
and show that this number is less than $4$. So the condition $X \geq C$ of Section 6 follows from $X \geq 200$.

*Hint.* Sum the geometric series in $j \geq 2$. The primes $2$, $3$, $5$, $7$ give less than $1.4$. For $p \geq 11$, use $p^{3/2} - p^{3/4} \geq 0.8\,p^{3/2}$, Chebyshev's bound $\theta(t) \leq t\log 4$, and partial summation: $\sum_{p > 10}\log p/p^{3/2} \leq \tfrac{3}{2}\int_{10}^\infty \theta(t)t^{-5/2}\,dt \leq 3\log 4/\sqrt{10} < 1.32$. A computation gives the value $1.96$ to two decimals.

**Exercise 5.** Deduce from the [theorem on windows](/decl/New.exists_prime_modEq_one_log_mem/) for $Q = 4$ the following statement for $Q = 2$, which the source does not state. For every $A$ there is $W_0$ such that for $W \geq W_0$, every $k > 1$ with $2^k \leq W^A$ and every $U \in [W, W^A]$, some prime $p \equiv 1 \pmod{2^k}$ has $\log p \in [U, U + W]$. Then explain why the proof of Section 6 does not apply to $Q = 2$ directly.

*Hint.* Apply the theorem for $Q = 4$ with the exponent $A + 1$ and the modulus $4^j$, where $j = \max(2, \lceil k/2\rceil)$. Then $2^k \mid 4^j$ and $4^j \leq 16 \cdot 2^k \leq W^{A + 1}$ for large $W$. For the second part, the real characters modulo $2^k$ have conductors $1$, $4$, $8$, $8$, and $8$ does not divide $Q^2 = 4$.

**Exercise 6.** Show that the proof of Section 6 gives more than the theorem states: for every $A$ there is $W_0$ such that for $W \geq W_0$, every $k > 1$ with $Q^k \leq W^A$ and every $U$ with $W \leq U \leq \exp(\sqrt{W}/8)$, the window $[U, U + W]$ holds a prime $p \equiv 1 \pmod{Q^k}$. Which step changes, and which threshold?

*Hint.* The bound $U \leq W^A$ is used only in step 5 of the proof. With $X = \sqrt{W}$, the inequality $3U\varphi(q)e^2 < e^{X/4}$ follows from $3e^2X^{2A} < e^{X/8}$. The data do not need this, and the source does not state it.

**Exercise 7.** In Case 1 of the [bound on the circle](/decl/New.norm_sub_mul_sum_term_le/), the proof bounds $F(z)$ and $P(z)$ separately, and it does not use the tail of the series. Explain why the tail cannot be used there. Then show that the bound $|F(z) - zP(z)| \leq 3Ue^E$ in Case 1 holds for every $U \geq X^2$, whether or not the window holds a prime.

*Hint.* For $\operatorname{Re} z \leq 0$ the series $\sum a_q(n)n^{-1-z}$ diverges, since $\sum_{p \equiv 1} \log p/p$ diverges. The hypothesis on the window is used only for the terms of the tail.

## Notes and references

Newman's proof of the prime number theorem is D. J. Newman, *Simple analytic proof of the prime number theorem*, Amer. Math. Monthly 87 (1980), 693 to 696. J. Korevaar, *On Newman's quick way to the prime number theorem*, Math. Intelligencer 4 (1982), 108 to 115, discusses the method and its Tauberian background. D. Zagier, *Newman's short proof of the prime number theorem*, Amer. Math. Monthly 104 (1997), 705 to 708, gives the form of the Analytic Theorem stated in Section 4. The source uses a finite form of the method, with one circle and a Gaussian kernel. This book does not know a published source for this finite form, and it does not attribute it.

For the classical theory of Section 2: the prime number theorem for progressions and the theorem of Siegel and Walfisz are in H. Davenport, *Multiplicative Number Theory*, third edition, Chapters 20 to 22, with the zero-free region for $L(s, \chi)$ in Chapter 14 and the characters in Chapter 4. The theorem of Siegel and Walfisz is also H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I*, Corollary 11.19, with the theorem of Siegel in the same chapter. The source cites this corollary in the comment to its theorem on windows. The bound $\varphi(n) \gg n/\log\log n$, which is stronger than the lemma on Euler's function of Section 2, is Hardy and Wright, *An Introduction to the Theory of Numbers*, Theorem 328. Linnik's theorem is U. V. Linnik, Mat. Sb. 15 (1944), 139 to 178 and 347 to 368. For primes in short intervals see M. N. Huxley, Invent. Math. 15 (1972), 164 to 170, and R. C. Baker, G. Harman and J. Pintz, Proc. London Math. Soc. (3) 83 (2001), 532 to 562. Cramér's conjecture on gaps between primes is H. Cramér, Acta Arith. 2 (1936), 23 to 46.

The use of power moduli to avoid exceptional zeros has a simple reason in the source: the real characters modulo $Q^k$ come from $Q^2$ (Section 3). The textbooks treat all moduli at once, and so they need the theorem of Siegel. The data of the argument need only the moduli $q_2^2 = (q_0d)^{2(s + 6)}$, so the special case is enough.

The theorem on windows does not depend on GRH or on any hypothesis on zeros. Lean accepts it if the checks that the source reports hold. This book did not rerun the checks.

Status: drafted by a model. No person has checked this chapter against the Lean source.
