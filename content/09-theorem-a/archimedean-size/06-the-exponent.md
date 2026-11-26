---
title: The exponent
lean:
  - New/UpperBound/Size/ArchimedeanSize.lean
decls:
  - New.Data.jetSize_sub_mainPrimeSum_le
  - New.Data.mul_jetSize_sub_mainPrimeSum_sub_le
  - New.Data.card_aPlaces_mul_excess_le
  - New.Data.two_mul_sum_gain_mul_log
  - New.Data.mainAmount_sub_add_two_mul_sum_gain
  - New.Data.chainSize_sub_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The exponent

Section 5 bounds the sizes of all rows by $\mathrm{chainSize}$ plus an error. The restriction to $Y_m$ removes $\#\Phi_a\,a\log N$ from the exponent. This section shows that the difference is the exponent $\mathrm{main} - m\cdot\mathrm{rem} + 2\sum_p\mathrm{gain}_p\log p$ of Theorem A, up to $32fa\log b$. The proof has two parts. The prime sums cancel exactly. The jet size $s_\infty(a)$ of a first row is paid by the expected value $s_{\mathrm{main}}$ and the level $N$.

[The prime sums](/chapter/prime-sums/) states the four results of the first two subsections as forward results. This section proves them.

### Notation

The definitions are those of [the prime sums](/chapter/prime-sums/):

- the direction amount $\mathrm{dir} = \sum_{\sigma\in\Phi}\bigl(s_\infty(\kappa(\sigma)) - s_{\mathrm{fin}}(\kappa(\sigma),\sigma)\bigr)$;
- the main amount $\mathrm{main} = mk\cdot\mathrm{dir}$;
- the expected value $s_{\mathrm{main}} = a\bigl(\log a - w + c_1\bigr)$, with $w = f^{-1}\sum_{\tau\in\Phi}\log\kappa(\tau)$ and $c_1 = \operatorname{Re}G_1(1)$;
- the total remainder $\mathrm{rem} = \sum_{\tau\in\Phi_a}\bigl(s_{\mathrm{fin}}(a,\tau) - s_{\mathrm{main}}\bigr)$.

The period is $\Omega = e^{C_d}\cdot 2\pi/\mathrm{rd}_E$ ([the primes, the level and the period](/chapter/data-and-sizes/#the-primes-the-level-and-the-period)), and $c_1 = -1 - C_d$ (`New.re_logDerivMean_one`, [notation](/chapter/notation/)). Put
$$G = \log\frac{M\,\mathrm{rd}_E}{2\pi}.$$
The table of sizes gives $|G| \le 23\log b$ (`New.Data.abs_log_M_mul_rootDisc_le`).

### The excess of one first row

**Proposition (Excess of one lift).**
$$s_\infty(a) - s_{\mathrm{main}} \le a(w + G) + 1 + \tfrac12\log a .$$

Lean: `New.Data.jetSize_sub_mainPrimeSum_le` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* *Stirling.* Let $S_n = n!/(\sqrt{2n}(n/e)^n)$ be the Stirling sequence. Its logarithm decreases in $n \ge 1$ (Mathlib, `Stirling.log_stirlingSeq'_antitone`), so $\log S_a \le \log S_1 = 1 - \tfrac12\log 2$, as $a \ge 1$. Write out $\log S_a = \log a! - \tfrac12(\log 2 + \log a) - a(\log a - 1)$. So
$$\log a! \le 1 - \tfrac12\log 2 + a(\log a - 1) + \tfrac12(\log 2 + \log a) = a\log a - a + 1 + \tfrac12\log a .$$

*The period.* From the definition of $\Omega$ and $c_1 = -1 - C_d$,
$$\log\frac M\Omega = \log M - C_d - \log 2\pi + \log\mathrm{rd}_E = 1 + c_1 + G .$$

*The difference.* Insert both:
$$s_\infty(a) - s_{\mathrm{main}} = \log a! + a(1 + c_1 + G) - a(\log a - w + c_1) \le a(w + G) + 1 + \tfrac12\log a .$$
The terms $a\log a$, $a$ and $ac_1$ cancel. $\square$

The proof shows the purpose of the constant $c_1$ in $s_{\mathrm{main}}$ and of the factor $e^{C_d}$ in $\Omega$. The two constants cancel. Only $a(w + G)$ remains, and the level $N$ is chosen to absorb it.

**Proposition (The level absorbs the excess).**
$$m\bigl(s_\infty(a) - s_{\mathrm{main}}\bigr) - a\log N \le 32\,a\log b .$$

Lean: `New.Data.mul_jetSize_sub_mainPrimeSum_sub_le` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* *The level.* The data put $\log N$ in the window $[\log N_-, \log N_- + \sqrt{\log b}]$, with
$$\log N_- = mw + (m - 1)G - \tfrac{15}2\log b$$
([the primes, the level and the period](/chapter/data-and-sizes/#the-primes-the-level-and-the-period); Lean: `New.Data.log_N_mem_Icc_logLevelTarget`). So
$$\log N \ge m(w + G) - \bigl(G + \tfrac{15}2\log b\bigr).$$

*The bound.* By the last proposition and $m, a \ge 0$,
$$m\bigl(s_\infty(a) - s_{\mathrm{main}}\bigr) - a\log N \le m\bigl(a(w + G) + 1 + \tfrac12\log a\bigr) - a\bigl(m(w + G) - G - \tfrac{15}2\log b\bigr).$$
The terms $ma(w + G)$ cancel, and the right side is
$$m\bigl(1 + \tfrac12\log a\bigr) + a\bigl(G + \tfrac{15}2\log b\bigr).$$
The table of sizes gives $m(1 + \tfrac12\log a) \le a\log b$, since $m \le 2\sqrt x$ and $\log a \le 2\log b$, while $a = xb$. With $G \le 23\log b$ and $\tfrac{15}2 \le 8$, the sum is at most $a\log b + 31a\log b = 32a\log b$. $\square$

**Corollary (All $a$-places).**
$$\#\Phi_a\Bigl(m\bigl(s_\infty(a) - s_{\mathrm{main}}\bigr) - a\log N\Bigr) \le 32\,fa\log b .$$

Lean: `New.Data.card_aPlaces_mul_excess_le` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* Multiply the last proposition by $\#\Phi_a \ge 0$, and use $\#\Phi_a \le f$ and $32a\log b \ge 0$. $\square$

### The prime sums cancel

**Proposition (Gains and prime sums).**
$$2\sum_{p\in\mathcal S}\mathrm{gain}_p\log p = m\sum_{\tau\in\Phi_a}s_{\mathrm{fin}}(a,\tau) + mk\sum_{\tau\in\Phi}s_{\mathrm{fin}}(\kappa(\tau),\tau).$$

Lean: `New.Data.two_mul_sum_gain_mul_log` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* *All primes below $x_1$.* The set $\mathcal S$ is the set of primes $p < \lceil x_1\rceil$ with $\chi_K(p) \ne 1$. At a prime with $\chi_K(p) = 1$ the gain is $0$, by the lemma on vanishing gain of Section 4. So the left side is the same sum over all primes $p < \lceil x_1\rceil$.

*Group by primes.* By the theorem on the prime sum grouped by primes of Section 4, with $U = \lceil x_1\rceil$ and $y = a$ or $y = \kappa(\tau) \le a$,
$$\sum_{\tau\in\Phi_a}s_{\mathrm{fin}}(a,\tau) = \sum_{p<\lceil x_1\rceil}\sum_{\tau\in\Phi_a}2\,s_p(a,\tau)\log p,\qquad \sum_\tau s_{\mathrm{fin}}(\kappa(\tau),\tau) = \sum_{p<\lceil x_1\rceil}2F(p)\log p .$$

*Compare term by term.* For each prime $p$,
$$2\,\mathrm{gain}_p\log p = 2m\Bigl(\sum_{\tau\in\Phi_a}s_p(a,\tau) + kF(p)\Bigr)\log p = m\sum_{\tau\in\Phi_a}2\,s_p(a,\tau)\log p + mk\cdot 2F(p)\log p .$$
Sum over $p$. $\square$

**Proposition (The exponent without prime sums).**
$$\mathrm{main} - m\cdot\mathrm{rem} + 2\sum_{p\in\mathcal S}\mathrm{gain}_p\log p = m\,\#\Phi_a\,s_{\mathrm{main}} + mk\sum_{\tau\in\Phi}s_\infty(\kappa(\tau)).$$

Lean: `New.Data.mainAmount_sub_add_two_mul_sum_gain` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* Write the three terms of the left side out:
$$\mathrm{main} = mk\sum_\tau s_\infty(\kappa(\tau)) - mk\sum_\tau s_{\mathrm{fin}}(\kappa(\tau),\tau),$$
$$m\cdot\mathrm{rem} = m\sum_{\tau\in\Phi_a}s_{\mathrm{fin}}(a,\tau) - m\,\#\Phi_a\,s_{\mathrm{main}},$$
and the gains are given by the last proposition. The prime sums $s_{\mathrm{fin}}(\kappa(\tau),\tau)$ cancel between $\mathrm{main}$ and the gains. The prime sums $s_{\mathrm{fin}}(a,\tau)$ cancel between $-m\cdot\mathrm{rem}$ and the gains. What remains is the right side. $\square$

The proposition explains the shape of the definitions. The first row of each diagram at an $a$-place gives the prime sum $s_{\mathrm{fin}}(a,\tau)$, and the next $k - 1$ rows give $s_{\mathrm{fin}}(\kappa(\tau),\tau)$. The second kind is already in the main amount. The first kind is in $m\cdot\mathrm{rem}$, after the subtraction of the expected value. This is why $\mathrm{rem}$ is a sum over $\Phi_a$ only.

### The exponent of the chain

**Theorem (The exponent of the chain).**
$$\mathrm{chainSize} - \#\Phi_a\,a\log N \le \mathrm{main} - m\cdot\mathrm{rem} + 2\sum_{p\in\mathcal S}\mathrm{gain}_p\log p + 32\,fa\log b .$$

Lean: `New.Data.chainSize_sub_le` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* By the last proposition, the right side is
$$m\,\#\Phi_a\,s_{\mathrm{main}} + mk\sum_\tau s_\infty(\kappa(\tau)) + 32\,fa\log b .$$
The left side is $m\,\#\Phi_a\,s_\infty(a) + mk\sum_\tau s_\infty(\kappa(\tau)) - \#\Phi_a\,a\log N$. The difference of the left and the right side is
$$\#\Phi_a\Bigl(m\bigl(s_\infty(a) - s_{\mathrm{main}}\bigr) - a\log N\Bigr) - 32\,fa\log b \le 0,$$
by the corollary on all $a$-places. $\square$

**Remark (Formalization).** The constant $c_1$ is `(logDerivMean P.d 1 1).re` in the source, and the proof rewrites it with `New.re_logDerivMean_one`. The Stirling bound is taken from Mathlib, not proved again. The bound $m(1 + \tfrac12\log a) \le a\log b$ and the bound $\#\Phi_a \le f$ are the only places where sizes enter; the rest is linear algebra in the reals, closed by `linarith` and `ring`. The sum over $\mathcal S$ in the source is a sum over a `Finset` filtered from `range ⌈x₁⌉₊`. The proof removes the filter $\chi_K(p) \ne 1$ because the gain vanishes at split primes. The cutoff $p < \lceil x_1\rceil$ stays.

### An example of the cancellation

Take one $a$-place $\tau$ and one lift, and look only at the first row. Its size is $s_\infty(a) = \log a! + a\log(M/\Omega)$, about $a\log a + a\log(M/\Omega)$. The divisibility side gives back $s_{\mathrm{fin}}(a,\tau)$. On average over the places this is about $s_{\mathrm{main}} = a(\log a - w + c_1)$. So the excess is about
$$a\log(M/\Omega) + a(w - c_1) - a = a(w + G),$$
since $\log(M/\Omega) = 1 + c_1 + G$. The term $a\log a$ of the factorial is matched by the term $a\log a$ of the prime sum: since $\sum_{\nu\le a}\Lambda(\nu)/\nu = \log a + O(1)$ by Mertens. The factor $1 - \chi_K(\nu)$ has mean $1$, and the weights shift the terms by $w$. With $m$ lifts, the excess $ma(w + G)$ is the term $a\cdot m(w + G)$ of $a\log N$, and $N$ is chosen for this. The rest, at most $32a\log b$ for each $a$-place, goes into the error.
