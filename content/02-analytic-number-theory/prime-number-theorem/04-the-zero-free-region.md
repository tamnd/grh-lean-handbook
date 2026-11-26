---
title: The zero-free region
lean:
  - Lib/Analytic/PrimeNumberTheorem/ZeroFreeRegion.lean
decls:
  - New.eventually_le_norm_regularL
  - New.pow_three_le_mul_norm_regularL_pow
  - New.div_pow_le_norm_regularL
  - New.norm_logDeriv_regularL_le
  - New.norm_logDeriv_entireL_le
  - New.eventually_norm_logDeriv_entireL_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The zero-free region

This section proves that $\tilde L(s, \chi)$ has no zero in the region $\operatorname{Re} s \geq 1 - l^{-25}$, $|s| \leq e^l$, for all large $l$, and that its logarithmic derivative is at most $2l^{25}$ there. The proof uses the inequality (2.1) of Mathlib, the growth bounds of Section 3, and one step to the left of length $2l^{-25}$. It does not use the Hadamard product. Section 6 and Volume 1 use the result to bound the transform of the prime remainder, and Chapter 5 uses its uniform form for primes in windows.

### The textbook form and the form here

The classical region is $\sigma \geq 1 - c/\log(q(|t| + 2))$, with one possible exception (Section 2). Put $T = e^l$. The region of the source is
$$\sigma \geq 1 - (\log T)^{-25}, \qquad |s| \leq T.$$
For a fixed $q$ and $|t| \leq T$ it is contained in the classical region for large $T$, with room to spare: $(\log T)^{-25}$ is much smaller than $c/\log(qT)$. So the source proves a weaker statement. It also proves the bound $|\tilde L'/\tilde L| \leq 2(\log T)^{25}$ in the region; the classical bound is $O(\log(qT))$ in a slightly smaller region (Davenport, Chapter 19, and Montgomery and Vaughan, Chapter 11). The proof of the weak form is close to the first proofs of a region of this shape for $\zeta$, which bound $|\zeta|$ and $|\zeta'|$ and use (2.1) with absolute values. Titchmarsh, *The Theory of the Riemann Zeta-Function*, Section 3.6, proves a region $\sigma \geq 1 - A(\log t)^{-9}$ for $\zeta$ in this way.

### The inequality of Mathlib

**Theorem (The 3-4-1 inequality).** Let $\chi$ be a character modulo $q$, let $x > 0$ and let $y$ be real. Then
$$\Big|L(1 + x, \chi_0)^3\, L(1 + x + iy, \chi)^4\, L(1 + x + 2iy, \chi^2)\Big| \geq 1,$$
where each $L$ is the Dirichlet series $\sum_n \chi(n) n^{-s}$.

Mathlib: `DirichletCharacter.norm_LSeries_product_ge_one`.

The proof in Mathlib is the classical one of Section 2: the logarithm of the left side is a sum over primes of terms $\operatorname{Re}(3 + 4 z + z^2)$-type expressions with $|z| = 1$ times positive weights, and each is nonnegative.

### Lower bounds to the right of the line

**Lemma (The 3-4-1 bound).** Let $\chi$ be a character modulo $q$. Let $l \geq 10^{10}$, $q \leq e^l$ and $0 < \eta \leq 1$. Let $s$ satisfy $\operatorname{Re} s \geq 1 + \eta$ and $|s| \leq \frac{3}{2}e^l$. If $\chi^2 = \chi_0$, assume that $|s - 1| \geq 1/l$. Then
$$\eta^3 \leq 256\, l^7\, |f_\chi(s)|^4.$$

Lean: `New.pow_three_le_mul_norm_regularL_pow` (Lib/Analytic/PrimeNumberTheorem/ZeroFreeRegion.lean).

*Proof.* Let $\sigma = \operatorname{Re} s$ and $s_2 = \sigma + 2i\operatorname{Im} s$. Then $|s_2| \leq 2|s| \leq 3e^l$, and
$$|s_2 - 1|^2 = |s - 1|^2 + 3(\operatorname{Im} s)^2 \geq |s - 1|^2.$$
The 3-4-1 inequality with $x = \sigma - 1$ and $y = \operatorname{Im} s$ gives
$$1 \leq |L(\sigma, \chi_0)|^3\, |L(s, \chi)|^4\, |L(s_2, \chi^2)|.$$
We bound the three factors.

1. By [the series near the line](/decl/New.norm_LSeries_char_le/) with $A = 1/\eta$, $|L(\sigma, \chi_0)| \leq 1 + 1/\eta \leq 2/\eta$.
2. If $\chi = \chi_0$, then $\chi^2 = \chi_0$, so $|s - 1| \geq 1/l$. By [the lemma from the series to $f_\chi$](/decl/New.norm_LSeries_le_mul_norm_regularL/), $|L(s, \chi)| \leq 2l\,|f_\chi(s)|$.
3. If $\chi^2 = \chi_0$, then $|s_2 - 1| \geq |s - 1| \geq 1/l$. So the same lemma gives $|L(s_2, \chi^2)| \leq 2l\,|f_{\chi^2}(s_2)|$. Since $\operatorname{Re} s_2 > 1$ and $|s_2| \leq 3e^l$, [growth near the line](/decl/New.norm_regularL_le_sq/) gives $|f_{\chi^2}(s_2)| \leq l^2$. So $|L(s_2, \chi^2)| \leq 2l^3$.

Multiply: $1 \leq (2/\eta)^3 (2l|f_\chi(s)|)^4 \cdot 2l^3 = 256\, l^7 |f_\chi(s)|^4/\eta^3$. $\square$

The bound $|L(\sigma, \chi_0)| \leq 2/\eta$ is the pole of order $3$ in the classical argument. The factor $|L(s_2, \chi^2)|$ is where a real character is special: if $\chi^2 = \chi_0$ and $s$ is near $1$, then $s_2$ is near the pole of $L(s, \chi_0)$, and the third factor is large. The hypothesis $|s - 1| \geq 1/l$ keeps $s_2$ away from the pole.

**Lemma (A lower bound to the right of the line).** Let $\chi$ be a character modulo $q$, let $l \geq 10^{10}$ and $q \leq e^l$. If $\chi^2 = \chi_0$, assume that $|f_\chi(z)| \geq 1/l$ for every $z$ with $|z - 1| \leq 1/l$. Let $\operatorname{Re} s \geq 1 + l^{-25}$ and $|s| \leq \frac{3}{2}e^l$. Then
$$|f_\chi(s)| \geq 12\, l^{-22}.$$

Lean: `New.div_pow_le_norm_regularL` (Lib/Analytic/PrimeNumberTheorem/ZeroFreeRegion.lean).

*Proof.* There are two cases.

*Case 1: $\chi^2 \neq \chi_0$, or $|s - 1| \geq 1/l$.* Apply [the 3-4-1 bound](/decl/New.pow_three_le_mul_norm_regularL_pow/) with $\eta = l^{-25}$. It gives $l^{-75} \leq 256\, l^7 |f_\chi(s)|^4$. Since $256 \cdot 12^4 \leq l^6$,
$$256\, l^7 \Big(\frac{12}{l^{22}}\Big)^4 = \frac{256 \cdot 12^4}{l^{81}} \leq \frac{1}{l^{75}} \leq 256\, l^7 |f_\chi(s)|^4,$$
and $|f_\chi(s)| \geq 12\,l^{-22}$.

*Case 2: $\chi^2 = \chi_0$ and $|s - 1| < 1/l$.* By the hypothesis, $|f_\chi(s)| \geq 1/l \geq 12\,l^{-22}$. $\square$

### The step to the left

**Lemma (The zero-free region for $f_\chi$).** Let $\chi$, $l$ and $q$ be as in the last lemma, with the same hypothesis if $\chi^2 = \chi_0$. Let $\operatorname{Re} s \geq 1 - l^{-25}$ and $|s| \leq e^l$. Then $f_\chi(s) \neq 0$, and
$$\Big|\frac{f_\chi'(s)}{f_\chi(s)}\Big| \leq l^{25}.$$

Lean: `New.norm_logDeriv_regularL_le` (Lib/Analytic/PrimeNumberTheorem/ZeroFreeRegion.lean).

*Proof.* Let $\eta = l^{-25}$. Since $l \geq 6$, $\eta \leq 1/(6l)$. Let $v = s + 2\eta$, a real step to the right.

*The disc.* Every $z$ with $|z - s| \leq 2\eta$ has $\operatorname{Re} z \geq 1 - 3\eta \geq 1 - 1/(2l)$ and $|z| \leq e^l + 2\eta \leq 2e^l$. So [the derivative bound](/decl/New.norm_deriv_regularL_le/) gives $|f_\chi'(z)| \leq 2l^3$ on the disc. The disc is convex, so
$$|f_\chi(v) - f_\chi(s)| \leq 2l^3 \cdot 2\eta = 4\, l^{-22}.$$

*The point $v$.* It has $\operatorname{Re} v \geq 1 + \eta$ and $|v| \leq e^l + 2\eta \leq \frac{3}{2}e^l$. By [the lower bound to the right](/decl/New.div_pow_le_norm_regularL/), $|f_\chi(v)| \geq 12\,l^{-22}$.

So $|f_\chi(s)| \geq 12\,l^{-22} - 4\,l^{-22} = 8\,l^{-22} > 0$, and
$$\Big|\frac{f_\chi'(s)}{f_\chi(s)}\Big| \leq \frac{2l^3}{8\,l^{-22}} = \frac{l^{25}}{4} \leq l^{25}. \qquad \square$$

Here is a picture in words. Stand at $s$, just to the left of the line, and look at the point $v$ at distance $2l^{-25}$ to the right. At $v$ the function is at least $12\,l^{-22}$, by (2.1). Between $s$ and $v$ it can move by at most $4\,l^{-22}$, because its derivative is at most $2l^3$. So it cannot reach $0$ at $s$. The exponent $25$ is where the two powers match: a step of length $l^{-a}$ costs $l^{3 - a}$ times a constant, and the lower bound from (2.1) is of the order $l^{-(3a + 7)/4}$. The step wins if $3 - a < -(3a + 7)/4$, that is, if $a > 19$. Exercise 2 asks for the details.

**Proposition (The zero-free region for $\tilde L$, uniform form).** Let $\chi$ be a character modulo $q \geq 1$, let $l \geq 10^{10}$ and $q \leq e^l$. If $\chi^2 = \chi_0$, assume that $|f_\chi(z)| \geq 1/l$ for every $z$ with $|z - 1| \leq 1/l$. Then for every $s$ with $\operatorname{Re} s \geq 1 - l^{-25}$ and $|s| \leq e^l$,
$$\tilde L(s, \chi) \neq 0 \quad \text{and} \quad \Big|\frac{\tilde L'(s, \chi)}{\tilde L(s, \chi)}\Big| \leq 2\,l^{25}.$$

Lean: `New.norm_logDeriv_entireL_le` (Lib/Analytic/PrimeNumberTheorem/ZeroFreeRegion.lean).

*Proof.* Write $\tilde L(s, \chi) = f_\chi(s)\, u(s)$, with $u(s) = s$ if $\chi = \chi_0$ and $u(s) = 1$ otherwise. In the region $\operatorname{Re} s \geq 1 - l^{-25} \geq 1/2$, so $u(s) \neq 0$ and $|u'/u| \leq 1/|s| \leq 2$. By [the zero-free region for $f_\chi$](/decl/New.norm_logDeriv_regularL_le/), $f_\chi(s) \neq 0$ and $|f_\chi'/f_\chi| \leq l^{25}$. So $\tilde L(s, \chi) \neq 0$, and $|\tilde L'/\tilde L| \leq l^{25} + 2 \leq 2l^{25}$. $\square$

The proposition is explicit and uniform: the threshold $10^{10}$ and the bound $2l^{25}$ do not depend on $q$ or $\chi$, and the only condition on the modulus is $q \leq e^l$. The one hypothesis that is not explicit is the lower bound near $1$ for a real character. The next lemma gives it for one fixed character.

### Real characters near the point 1

**Lemma (No small values near 1).** Let $\chi$ be a character modulo $q \geq 1$. There is $r_0 > 0$ such that for every real $r$ with $|r| < r_0$ and every $s$ with $|s - 1| \leq r$, one has $|f_\chi(s)| \geq r$.

Lean: `New.eventually_le_norm_regularL` (Lib/Analytic/PrimeNumberTheorem/ZeroFreeRegion.lean).

*Proof.* By [the lemma on $\operatorname{Re} s \geq 1$](/decl/New.entireL_ne_zero/), $f_\chi(1) = \tilde L(1, \chi) \neq 0$. This uses Dirichlet's theorem $L(1, \chi) \neq 0$ for $\chi \neq \chi_0$, from Mathlib. By continuity there is a disc about $1$ on which $|f_\chi| \geq |f_\chi(1)|/2$. Take $r_0$ at most the radius of this disc and at most $|f_\chi(1)|/2$. $\square$

For $r \leq 0$ the statement is empty or trivial, and the source states it for $r$ near $0$ in $\mathbb{R}$ (a filter `𝓝 0`). Only small positive $r$ matter.

**Example.** Let $q = 1$. Then $\chi = \chi_0 = \chi^2$, and $f_\chi(s) = (s - 1)\zeta(s)/s$. Near $s = 1$, $(s - 1)\zeta(s) = 1 + \gamma(s - 1) + O(|s - 1|^2)$, with Euler's constant $\gamma$, so $f_\chi(s) = 1 + (\gamma - 1)(s - 1) + O(|s - 1|^2)$. Hence $|f_\chi(s)| \geq 1/2$ for $|s - 1|$ small, and the lemma holds with an explicit $r_0$. For a real nonprincipal $\chi$, the lemma rests on $L(1, \chi) > 0$, and the size of $r_0$ depends on the size of $L(1, \chi)$ and of $L'$ near $1$. This is the quantity of Siegel's theorem. For one fixed $\chi$ it is one positive number, and nothing more is needed.

**Theorem (The zero-free region).** Let $\chi$ be a character modulo $q \geq 1$. There is $l_0$ such that for every $l \geq l_0$ and every $s$ with $\operatorname{Re} s \geq 1 - l^{-25}$ and $|s| \leq e^l$,
$$\tilde L(s, \chi) \neq 0 \quad \text{and} \quad \Big|\frac{\tilde L'(s, \chi)}{\tilde L(s, \chi)}\Big| \leq 2\,l^{25}.$$

Lean: `New.eventually_norm_logDeriv_entireL_le` (Lib/Analytic/PrimeNumberTheorem/ZeroFreeRegion.lean).

*Proof.* Take $l_0$ so large that $l_0 \geq 10^{10}$, $l_0 \geq q$, and $1/l_0 < r_0$ for the $r_0$ of [the last lemma](/decl/New.eventually_le_norm_regularL/). For $l \geq l_0$: $q \leq l \leq e^l$, and with $r = 1/l$ the lemma gives the hypothesis of [the uniform form](/decl/New.norm_logDeriv_entireL_le/) for real characters. Apply it. $\square$

**Remark (Formalization).** The threshold $l_0$ depends on $\chi$, through $r_0$, and not only on $q$. For a character with $\chi^2 \neq \chi_0$ the uniform form needs no hypothesis, and $l_0 = \max(10^{10}, q)$ works. For a real character, $r_0$ is chosen by continuity, and the source gives no formula for it. So the theorem is not effective in $\chi$, in the same sense as the theorem of Siegel and Walfisz, but for a simpler reason: the argument uses $f_\chi(1) \neq 0$ and continuity, and asks for no lower bound in terms of $q$. Volume 1 applies the theorem to the finitely many characters modulo $q$ and $qd$ for two fixed $q$, so one $l_0$ serves all of them. Chapter 5 applies [the uniform form](/decl/New.norm_logDeriv_entireL_le/) to characters modulo $M^k$ for unbounded $k$. There the real characters modulo $M^k$ come from the fixed modulus $M^2$ when $4 \mid M$, so finitely many values $r_0$ serve all $k$ (`New.eventually_norm_logDeriv_entireL_le_near_one`, stated in Volume 1, [the data exist](/chapter/data-exist/)).

**Remark (Formalization).** The theorem uses a disc $|s| \leq e^l$, not a rectangle $|t| \leq T$. For $\operatorname{Re} s \leq 2$ the two differ only by a factor of about $1$ in $T$, so nothing is lost. The theorem also covers the part of the disc with $\operatorname{Re} s \geq 1$. There the non-vanishing is classical, but the bound $2l^{25}$ for the logarithmic derivative is new information. The Tauberian theorem of Section 5 needs a bound for its function on the whole region $\operatorname{Re} s \geq 1 - l^{-A}$, $|s| \leq e^l$, and this includes points far to the right of the line.
