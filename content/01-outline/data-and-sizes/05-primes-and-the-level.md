---
title: The primes, the level and the period
lean:
  - New/Reduction/Data/AdmissibleData.lean
  - New/Reduction/Data/Magnitudes.lean
  - New/Reduction/Data/LevelAndTwists.lean
  - New/Reduction/Data/Sizes.lean
  - New/Derivatives/Field/ChosenPlaces.lean
  - New/UpperBound/Size/ArchimedeanSize.lean
decls:
  - New.Data.levelPrime
  - New.Data.M_mem_Icc
  - New.Data.rootDisc_mem_Icc
  - New.Data.bigOmega_le_one
  - New.Data.log_M_div_bigOmega_mem_Icc
  - New.Parameters.logLevelMin
  - New.Parameters.logLevelMin_mem_Icc
  - New.Data.N
  - New.Data.log_N_mem_Icc
  - New.Data.mul_jetSize_sub_mainPrimeSum_sub_le
  - New.Data.log_classNumber_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The primes, the level and the period

The last fields of the data are three primes: $p_0$ and $p_1$, whose product $M$ is the principal level of the theta lifts, and the level $N$. The logarithm of $N$ must lie in a window of width $\sqrt{\log b}$ above a number $\log N_-$ that the other data fix. This section bounds the primes and the period $\Omega$, and explains the formula for $N_-$.

### The primes of the principal level

**Definition (The primes of the principal level).** The data contain two distinct primes $p_0$, $p_1$ with
$$p_i \equiv 1 \pmod{q_2^2}, \qquad b^{10} \leq p_i \leq b^{11} \qquad (i = 0, 1),$$
and an integer $\bar\pi_M$ of $K$ with $\bar\pi_M \cdot \overline{\bar\pi_M} = p_0 p_1$. The principal level is $M = p_0 p_1$. The source writes $\pi_M$ for the conjugate of $\bar\pi_M$.

Lean: `New.Data.levelPrime`, `New.Data.levelPrime_prime`, `New.Data.levelPrime_modEq_one_q₂_sq`, `New.Data.levelPrime_injective`, `New.Data.levelPrime_mem`, `New.Data.piMBar`, `New.Data.piMBar_mul_star` (New/Reduction/Data/AdmissibleData.lean); `New.Data.M` (same file).

The source indexes the two primes by $\operatorname{Fin} 2$, so `levelPrime 0` is $p_0$ and `levelPrime 1` is $p_1$. The datum $\bar\pi_M$ says that $M = p_0 p_1$ is the norm of an integer of $K$. The data ask for $\bar\pi_M$ directly, so this chapter needs no argument for it. The construction in [the data exist](/chapter/data-exist/) takes $p_0$ and $p_1$ from windows for primes $\equiv 1 \pmod{q_2^2}$, and finds $\bar\pi_M$ by a pigeonhole argument in the class group of $K$.

**Lemma (The primes and $M$).** For $i = 0, 1$:

1. $p_i \equiv 1 \pmod{q_1 d}$, and $q_2^2 \mid p_i - 1$;
2. $b^{20} \leq M \leq b^{22}$;
3. $b^2 < p_i < N$.

Lean: `New.Data.levelPrime_modEq_one`, `New.Data.dvd_levelPrime_sub_one`, `New.Data.M_mem_Icc` (New/Reduction/Data/Magnitudes.lean); `New.Data.levelPrime_mem_Ioo` (New/Reduction/Data/Sizes.lean).

*Proof.* Part 1: $q_1 d \mid q_2 \mid q_2^2$ (`New.Parameters.q₁_mul_d_dvd_q₂`), and $p_i \geq 1$. Part 2: multiply the bounds for $p_0$ and $p_1$. Part 3: $b^2 < b^{10} \leq p_i$, since $b > 1$. For the upper bound, $\log N \geq m \log b \geq 10^4 \log b$ by the theorem on the level below, so $N \geq b^{101} > b^{11} \geq p_i$. $\square$

### The root discriminant and the period

The period of the field is
$$\Omega = \exp\bigl(c_{\mathrm{CS}}(d)\bigr) \cdot \frac{2\pi}{\mathrm{rd}_E},$$
where $c_{\mathrm{CS}}(d) = \gamma - \operatorname{Re}(L'/L)(1, \chi_K)$ and $\mathrm{rd}_E = \lvert d_E \rvert^{1/[E:\mathbb{Q}]}$ is the root discriminant (`New.Parameters.bigOmega`, `New.chowlaSelbergConst`). The source uses $\Omega$ only through its definition and the bounds below.

**Theorem (The root discriminant).** The root discriminant of $E$ satisfies
$$x^{10} \leq \mathrm{rd}_E \leq x^{12}.$$

Lean: `New.Data.rootDisc_mem_Icc` (New/Derivatives/Field/ChosenPlaces.lean).

The proof is in [the field E at the primes](/chapter/field-at-primes/) (Volume 9). It writes $\mathrm{rd}_E^{\,f} = \prod_v v(\delta_E)$, a product over the infinite places $v$, for an element $\delta_E$ of $E$, and bounds each factor below by $x^{10}$ and above by $x^{12}$ (`New.Data.hasLogBound_deltaE`). A cruder upper bound is $\mathrm{rd}_E \leq q_1 d$ (`New.rootDiscr_mem_Icc`), which the next theorem uses.

**Proposition (The size of $\Omega$).** The data satisfy:

1. $x^{-13} \leq \Omega \leq 1$;
2. $20 \log b \leq \log(M/\Omega) \leq 23 \log b$;
3. $\lvert \log(M \,\mathrm{rd}_E / 2\pi)\rvert \leq 23 \log b$.

Lean: `New.Data.bigOmega_le_one`, `New.Data.log_M_div_bigOmega_mem_Icc`, `New.Data.abs_log_M_mul_rootDisc_le` (New/Reduction/Data/Sizes.lean). The lower bound $x^{-13} \leq \Omega$ is an instance of `New.Data.HasLogBound` in New/Reduction/Data/LevelAndTwists.lean.

*Proof.* The constant terms are small. One has $\lvert c_{\mathrm{CS}}(d)\rvert \leq C_P$, and $1 \leq 2\pi \leq e^6$, so $\lvert c_{\mathrm{CS}}(d)\rvert + 6 \leq C_P + 6 \leq \log x$ by (S1) and (S2).

Part 1. One has $\log\Omega = c_{\mathrm{CS}}(d) + \log 2\pi - \log \mathrm{rd}_E$. By the theorem above, this is at most $\lvert c_{\mathrm{CS}}(d) \rvert + 6 - 10 \log x \leq 0$, and at least $-\lvert c_{\mathrm{CS}}(d)\rvert - 12 \log x \geq -13 \log x$.

Part 2. By part 1 and Lemma (The primes and $M$), $M/\Omega \geq M \geq b^{20}$, and $M/\Omega \leq b^{22} x^{13} \leq b^{23}$, since $13 \log x \leq \log b$.

Part 3. One has $M\,\mathrm{rd}_E/2\pi \geq b^{20} x^{10}/e^{2} \geq 1$ and $M\,\mathrm{rd}_E/2\pi \leq b^{22} x^{12} \leq b^{23}$. $\square$

The jet size of order $j$ is $s_\infty(j) = \log j! + j\log(M/\Omega)$ (`New.Data.jetSize`). The source calls it the size of a derivative of order $j$; Theorem A bounds the derivatives of order $j$ of the theta lifts in terms of it. By part 2 and $j! \leq j^j \leq (b^2)^j$ for $j \leq a \leq b^2$,
$$20\, j \log b \leq s_\infty(j) \leq 25\, j \log b \qquad (j \leq a)$$
(`New.Data.jetSize_mem_Icc`, New/Reduction/PrimeSums.lean).

### The lower end of the range for the level

The level $N$ must cancel the main term of the jet sizes. The source fixes the window for $\log N$ by a formula in the other data.

**Definition (The lower end $N_-$).** For an exponent $s$, a rank $m$, weights $\kappa : \Phi \to \mathbb{N}$, an integer $M$ and a real number $L$ put
$$\log N_- = m \cdot \frac{1}{f}\sum_{\tau \in \Phi} \log \kappa(\tau) + (m - 1) \log \frac{M\, \mathrm{rd}_E}{2\pi} - \frac{15}{2} L .$$
So $N_- = \bar\kappa^{\,m} (M\,\mathrm{rd}_E/2\pi)^{m-1} e^{-15L/2}$, where $\bar\kappa$ is the geometric mean of the weights.

Lean: `New.Parameters.logLevelMin` (New/Reduction/Data/AdmissibleData.lean); at the values of the data it is `New.Data.logLevelTarget` (New/Reduction/Data/LevelAndTwists.lean), with `New.Data.logLevelTarget_eq_logLevelMin`.

**Theorem (The size of $N_-$).** Let $s, m, M \in \mathbb{N}$, let $\kappa : \Phi(s) \to \mathbb{N}$ and $L \in \mathbb{R}$. Assume
$$2 \leq m, \qquad 7 \leq L, \qquad 1 \leq \kappa(\tau) \leq e^L \ (\tau \in \Phi), \qquad e^{20L} \leq M \leq e^{22L}, \qquad q_1 d \leq e^L .$$
Then
$$m L \leq \log N_- \leq 24\, m L .$$

Lean: `New.Parameters.logLevelMin_mem_Icc` (New/Reduction/Data/AdmissibleData.lean).

*Proof.* The idea is that each of the three terms has a known size: the mean of $\log\kappa$ lies in $[0, L]$, and the middle logarithm lies in $[19L, 23L]$.

First, $1 \leq \mathrm{rd}_E \leq q_1 d$ (`New.rootDiscr_mem_Icc`, with `New.Parameters.conductor_mem_differentIdeal`). The upper bound holds since the different of $E$ contains $q_1 d$. Second, the mean $w = \frac1f\sum_\tau \log\kappa(\tau)$ lies in $[0, L]$, since each $\log\kappa(\tau)$ does (`New.sum_log_div_card_mem_Icc`). Third, put $G = \log(M\,\mathrm{rd}_E/2\pi)$. From $M \geq e^{20L}$, $\mathrm{rd}_E \geq 1$ and $2\pi \leq e^{2} \leq e^L$ one gets $G \geq 19L$. From $M \leq e^{22L}$, $\mathrm{rd}_E \leq e^L$ and $2\pi \geq 1$ one gets $G \leq 23L$ (`New.log_mul_div_two_pi_mem_Icc`).

Lower bound: $\log N_- = m w + (m-1)G - \tfrac{15}2 L \geq 19(m - 1)L - \tfrac{15}{2}L$. This is at least $mL$ if $18 m \geq 26.5$, which holds for $m \geq 2$.

Upper bound: $\log N_- \leq mL + 23(m-1)L - \tfrac{15}2 L = 24 mL - 30.5 L \leq 24 mL$. $\square$

**Remark (Formalization).** The theorem does not use the data. It is stated for arbitrary $s$, $m$, $\kappa$, $M$ and $L$, so that the construction of the data in [the data exist](/chapter/data-exist/) can use it before the level exists. Exercise 5 shows that the hypothesis $m \geq 2$ is needed in some form. The hypotheses hold for the data with $L = \log b$: the weights lie in $[1, b]$, $M \in [b^{20}, b^{22}]$, and $q_1 d \leq x^{13} \leq b$.

### The level

**Definition (The level).** The data contain a prime $N$ with
$$N \equiv 1 \pmod{q_2^2}, \qquad \log N_- \leq \log N \leq \log N_- + \sqrt{\log b},$$
where $\log N_-$ is taken at the exponent $s$, the rank $m$, the weights $\kappa$, the integer $M = p_0p_1$ and $L = \log b$. The data also contain an integer $\pi_N$ of $E$ with $\pi_N \overline{\pi_N} = N$.

Lean: `New.Data.N`, `New.Data.N_prime`, `New.Data.N_modEq_one_q₂_sq`, `New.Data.log_N_mem`, `New.Data.piN`, `New.Data.piN_mul_star` (New/Reduction/Data/AdmissibleData.lean).

**Theorem (The size of the level).** The level satisfies:

1. $N \equiv 1 \pmod{q_1 d}$;
2. $m \log b \leq \log N_- \leq 24\, m\log b$;
3. $m \log b \leq \log N \leq 30\, m \log b$;
4. $\sqrt{x}\log b \leq \log N \leq e^{32}\sqrt{x}\log b$;
5. $b^{101} \leq N$.

Lean: `New.Data.N_modEq_one`, `New.Data.logLevelTarget_mem_Icc`, `New.Data.log_N_mem_Icc` (New/Reduction/Data/LevelAndTwists.lean). Parts 4 and 5 are instances of `New.Data.HasLogBound` in the same file.

*Proof.* Part 1 is the argument for the primes $p_i$. Part 2 is the theorem above with $L = \log b$. Its hypotheses: $m \geq 10^4 \geq 2$; $\log b \geq 7$; $1 \leq \kappa(\tau) \leq b$ by Section 4; $M \in [b^{20}, b^{22}]$; and $q_1 d \leq b$. Part 3 adds the width $\sqrt{\log b}$ of the window: $\sqrt{\log b} \leq \log b \leq 6 m \log b$, so the upper end is at most $(24 + 6) m \log b$. Part 4 follows from part 3 and $\sqrt x \leq m \leq 2\sqrt x$, since $\log 60 \leq 32$. Part 5: $\log N \geq m\log b \geq 10^4 \log b \geq 101 \log b$. $\square$

The construction in [the data exist](/chapter/data-exist/) takes $N$ from a window for primes $\equiv 1 \pmod{q_2^2}$, a consequence of the Siegel and Walfisz theorem, and $\pi_N$ from a sum of two squares. It needs the width $\sqrt{\log b}$ of the window, the modulus $q_2^2 \leq x^{66 q_0 d}$ (Section 3), and the upper bound $\log N_- \leq 24 m \log b$ for the start of the window.

### Why the level has this size

The formula for $N_-$ is chosen for one cancellation, which the archimedean part of Theorem A uses (Volume 9): the term $a\log N$ cancels $m$ times the excess $s_\infty(a) - s_{\mathrm{main}}$ of the jet size of order $a$ over the main prime sum.

**Theorem (The level compensates the excess).** With $s_{\mathrm{main}}$ as in Section 4,
$$m\bigl(s_\infty(a) - s_{\mathrm{main}}\bigr) - a \log N \leq 32\, a \log b,$$
and so
$$\#\Phi_a \Bigl( m\bigl(s_\infty(a) - s_{\mathrm{main}}\bigr) - a\log N \Bigr) \leq 32 f a \log b .$$

Lean: `New.Data.mul_jetSize_sub_mainPrimeSum_sub_le`, `New.Data.card_aPlaces_mul_excess_le` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* Put $w = \frac1f\sum_\tau\log\kappa(\tau)$ and $G = \log(M\,\mathrm{rd}_E/2\pi)$. The constant $c_1$ of $s_{\mathrm{main}}$ satisfies $c_1 = -1 - c_{\mathrm{CS}}(d)$ (`New.re_logDerivMean_one`). With the definition of $\Omega$ this gives $\log(M/\Omega) = 1 + c_1 + G$, so $c_1$ cancels in $s_\infty(a) - s_{\mathrm{main}}$. With Stirling's bound $\log a! \leq a \log a - a + 1 + \tfrac12\log a$, the excess is
$$s_\infty(a) - s_{\mathrm{main}} \leq a(w + G) + 1 + \tfrac12 \log a .$$
The lower end of the window gives $\log N \geq m(w + G) - (G + \tfrac{15}{2}\log b)$. So
$$m\bigl(s_\infty(a) - s_{\mathrm{main}}\bigr) - a\log N \leq m\bigl(1 + \tfrac12\log a\bigr) + a\bigl(G + \tfrac{15}2\log b\bigr).$$
The terms $m a (w + G)$ cancel. The first term is at most $a \log b$, and $G \leq 23 \log b$ by the proposition on $\Omega$. So the total is at most $a\log b + a(23 + 8)\log b = 32\, a\log b$. The second claim is the first one times $\#\Phi_a \leq f$. $\square$

The error $32 f a \log b$ is small against the error unit
$$\mathrm{err} = f\, a \log^3 b$$
(`New.Data.errorUnit`), the unit in which the source measures the losses of the argument. The main amount is at least $x^4 f a$ (`New.Data.le_mainAmount`, New/Reduction/PrimeSums.lean), and $\log^3 b \leq x^{3/100}$ by (S2). So the error unit is smaller than the main amount by a factor $x^{3.97}$ at least.

### The class number

**Proposition (The class number).** The data satisfy $\log h_E \leq x^{30}$.

Lean: `New.Data.log_classNumber_le` (New/Reduction/Data/Sizes.lean).

*Proof.* A number field $F$ of degree $n$ and discriminant $d_F$ has $h_F \leq (2^n \lvert d_F\rvert)^{n+1}$ (`New.classNumber_le`). This is a crude form of the Minkowski bound: each ideal class contains an integral ideal of norm at most $2^n\lvert d_F\rvert$, and there are few such ideals. For $E$ one has $n = 2f$ and $\lvert d_E\rvert = \mathrm{rd}_E^{\,2f}$. So
$$\log h_E \leq (2f + 1)\cdot 2f\,(\log 2 + \log \mathrm{rd}_E) \leq (2f + 1)\cdot 2f\cdot 13 \log x .$$
With $f \leq q_1 \leq x^{12}$ this is at most $78\, x^{24}\log x \leq x^{30}$. $\square$

The bound is far from the truth, but the argument needs only that $\log h_E$ is a fixed power of $x$. It is used in the existence of the fitted twists in Volume 12.
