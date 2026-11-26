---
title: The Dirichlet series and the constant
lean:
  - New/Reduction/Zeros/PrimeError.lean
  - Lib/Analytic/EntireLFunction.lean
  - Lib/General/NumberTheory/ImaginaryQuadraticField.lean
decls:
  - New.LSeriesHasSum_mul_vonMangoldt
  - New.LSeries_lambdaKResidueClass_eq_add_logDerivMean
  - New.analyticAt_logDerivMean_of_one_le_re
  - New.chowlaSelbergConst
  - New.re_logDerivMean_one
  - New.re_logDerivMean_one_eq_add_re_logDeriv
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Dirichlet series and the constant

This section is the first step of the plan. It writes the Dirichlet series of $\lambda$ through $G_q$, and it computes the constant $c_1$. The notation is that of Section 3.

### The logarithmic derivative of an L-function

**Lemma (The series of χΛ).** Let $\chi$ be a Dirichlet character modulo $N \geq 1$, and let $\operatorname{Re} s > 1$. Then the series $\sum_{n \geq 1} \chi(n)\Lambda(n) n^{-s}$ converges absolutely, and
$$\sum_{n \geq 1} \chi(n)\Lambda(n) n^{-s} = \frac{\delta_\chi}{s - 1} - \frac{\tilde L'}{\tilde L}(s, \chi), \qquad \delta_\chi = \begin{cases} 1 & \text{if } \chi \text{ is principal,} \\ 0 & \text{otherwise.} \end{cases}$$

Lean: `New.LSeriesHasSum_mul_vonMangoldt` (Lib/Analytic/EntireLFunction.lean).

*Proof.* For $\operatorname{Re} s > 1$, the Euler product gives $-L'/L(s, \chi) = \sum \chi(n)\Lambda(n) n^{-s}$, and $L(s, \chi) \neq 0$. Mathlib proves this identity. For a non-principal $\chi$, $\tilde L = L$. For a principal $\chi$, $\tilde L(s, \chi) = (s - 1)L(s, \chi)$, so $\tilde L'/\tilde L = 1/(s - 1) + L'/L$, and $-L'/L = 1/(s - 1) - \tilde L'/\tilde L$. $\square$

In this form the pole of $L(s, \chi_0)$ at $s = 1$ is explicit, and $\tilde L'/\tilde L$ is analytic on $\operatorname{Re} s \geq 1$ by [Lemma](/decl/New.entireL_ne_zero/).

### Orthogonality

The characters modulo $q$ detect the class $1$. For every $n \in \mathbb{N}$,
$$\frac{1}{\varphi(q)} \sum_{\psi \bmod q} \psi(n) = \begin{cases} 1 & \text{if } n \equiv 1 \bmod q, \\ 0 & \text{otherwise} \end{cases}$$
(Davenport, Chapter 4). If $\gcd(n, q) > 1$, every term is $0$. Also $\psi(n)\chi_K(n) = (\psi\chi_K)(n)$ by [Lemma](/decl/New.quadTwist_apply/). So
$$\lambda(n) = \frac{1}{\varphi(q)} \sum_{\psi \bmod q} \Bigl(\psi(n)\Lambda(n) - (\psi\chi_K)(n)\Lambda(n)\Bigr).$$

**Proposition (The Dirichlet series of the weight).** Let $d$ be an odd prime, let $q \geq 1$ with $\gcd(q, d) = 1$, and let $\operatorname{Re} s > 1$. Then
$$\sum_{n \geq 1} \lambda(n) n^{-s} = \frac{s}{\varphi(q)(s - 1)} + G_q(s).$$

Lean: `New.LSeries_lambdaKResidueClass_eq_add_logDerivMean` (New/Reduction/Zeros/PrimeError.lean).

*Proof.* Apply the lemma to $\psi$ and to $\psi\chi_K$, and subtract. By [Lemma](/decl/New.quadTwist_ne_one/), no twist $\psi\chi_K$ is principal, so the twists give no term $1/(s - 1)$. Among the $\psi$, only the principal character gives such a term. With the identity for $\lambda(n)$ above, the series of $\lambda$ converges absolutely, and its sum is
$$\frac{1}{\varphi(q)}\Bigl(\frac{1}{s - 1} + \sum_{\psi}\Bigl(\frac{\tilde L'}{\tilde L}(s, \psi\chi_K) - \frac{\tilde L'}{\tilde L}(s, \psi)\Bigr)\Bigr) = \frac{1}{\varphi(q)}\Bigl(\frac{1}{s - 1} + 1\Bigr) + G_q(s).$$
Finally $1/(s - 1) + 1 = s/(s - 1)$. $\square$

The hypotheses on $d$ enter only through [Lemma](/decl/New.quadTwist_ne_one/). If a twist were principal, the series would have an extra pole $-1/(\varphi(q)(s - 1))$ (Exercise 5).

**Remark (Formalization).** The source states the identity for `LSeries`, which is Mathlib's `tsum` of the terms $\lambda(n) n^{-s}$. A `tsum` of a series that is not summable has the value $0$. Here this convention plays no role: the proof shows that the series is summable for $\operatorname{Re} s > 1$, through the sum of the summable series of the lemma.

The $-1$ in $G_q$ splits the pole term in the form $s/(\varphi(q)(s - 1))$. After the kernel $1/(s(s - 1))$ of Section 2, this term is $1/(\varphi(q)(s - 1)^2)$, the transform of $\log y/\varphi(q)$ exactly. So all of the constant is in $G_q(1)$.

**Lemma (Analyticity on the line 1).** Let $q \geq 1$, and let $\operatorname{Re} s \geq 1$. Then $G_q$ is analytic at $s$.

Lean: `New.analyticAt_logDerivMean_of_one_le_re` (New/Reduction/Zeros/PrimeError.lean).

*Proof.* Each $\tilde L$ is entire ([Lemma](/decl/New.analyticAt_entireL/)) and has no zero at $s$ ([Lemma](/decl/New.entireL_ne_zero/)). So each $\tilde L'/\tilde L$ is analytic at $s$, and $G_q$ is a finite linear combination of them. $\square$

This lemma needs no hypothesis on $d$. The value $c_q = \operatorname{Re} G_q(1)$ is the value of an analytic function, and no convention $x/0 = 0$ enters it.

### The example q = 1

For $q = 1$ there is one character, the principal character $1$ modulo $1$, with $\tilde L(s, 1) = (s - 1)\zeta(s)$. The twist $1 \cdot \chi_K$ is $\chi_K$, as a character modulo $1 \cdot d = d$. So
$$G_1(s) = \frac{\tilde L'}{\tilde L}(s, \chi_K) - \frac{Z'}{Z}(s) - 1, \qquad Z(s) = (s - 1)\zeta(s).$$

**Example (The series for q = 1).** Let $d \equiv 3 \bmod 4$ be a prime, and let $K = \mathbb{Q}(\sqrt{-d})$. By quadratic reciprocity, the character $n \mapsto (-d/n)$ of $K$ equals $(n/d)$ at every $n \geq 1$. The number of ideals of norm $n$ in the ring of integers of $K$ is $\sum_{m \mid n} \chi_K(m)$. So $\zeta_K(s) = \zeta(s)L(s, \chi_K)$, and for $\operatorname{Re} s > 1$,
$$\sum_{n \geq 1} \lambda(n) n^{-s} = -\frac{\zeta'}{\zeta}(s) + \frac{L'}{L}(s, \chi_K) = -2\frac{\zeta'}{\zeta}(s) + \frac{\zeta_K'}{\zeta_K}(s).$$
The residue at $s = 1$ is $2 - 1 = 1$, the residue of $s/(s - 1)$. A zero of $\zeta$ of order $m$ is a pole with residue $-2m + m = -m$. A zero of $L(s, \chi_K)$ of order $m$ that is not a zero of $\zeta$ is a pole with residue $+m$. After the kernel $1/(s(s - 1))$, this gives the residues $\pm m/(\rho(1 - \rho))$ of the main theorem for $q = 1$.

### The Chowla-Selberg constant

**Definition (The Chowla-Selberg constant).** For a prime $d$ let
$$\mathrm{cs}_d = \gamma - \operatorname{Re} \frac{\tilde L'}{\tilde L}(1, \chi_K),$$
where $\chi_K = (\cdot/d)$ is a character modulo $d$ and $\gamma$ is Euler's constant. For odd $d$, $\chi_K$ is not principal, $\tilde L = L$, and $L'/L(1, \chi_K)$ is real, since $\chi_K$ is real. So $\mathrm{cs}_d = \gamma - L'/L(1, \chi_K)$.

Lean: `New.chowlaSelbergConst` (Lib/General/NumberTheory/ImaginaryQuadraticField.lean).

**Proposition (The constant for q = 1).** Let $d$ be a prime. Then
$$c_1 = \operatorname{Re} G_1(1) = -1 - \gamma + \operatorname{Re} \frac{\tilde L'}{\tilde L}(1, \chi_K) = -1 - \mathrm{cs}_d.$$

Lean: `New.re_logDerivMean_one` (New/Reduction/Zeros/PrimeError.lean), with `New.re_logDerivMean_one_eq_add_re_logDeriv` for the middle form.

*Proof.* By the Laurent expansion $\zeta(s) = 1/(s - 1) + \gamma + O(s - 1)$, $Z(s) = 1 + \gamma(s - 1) + O((s - 1)^2)$. So $Z(1) = 1$, $Z'(1) = \gamma$ and $Z'/Z(1) = \gamma$. Put $s = 1$ in the formula for $G_1$ and take real parts. $\square$

The constant has a closed form through the Gamma function, which explains the name. The source does not prove it and does not use it.

**Example (A formula with Gamma values).** Let $d > 3$ be a prime with $d \equiv 3 \bmod 4$, and let $h$ be the class number of $K = \mathbb{Q}(\sqrt{-d})$. Then
$$\mathrm{cs}_d = -\log 2\pi + \frac{1}{h}\sum_{a = 1}^{d - 1} \chi_K(a) \log\Gamma\Bigl(\frac{a}{d}\Bigr).$$
*Derivation.* Write $L(s, \chi_K) = d^{-s}\sum_{a = 1}^{d - 1} \chi_K(a)\zeta(s, a/d)$ with the Hurwitz zeta function. The values $\zeta(0, x) = 1/2 - x$ and $\partial_s \zeta(0, x) = \log\Gamma(x) - \frac{1}{2}\log 2\pi$ (Lerch) give $L(0, \chi_K) = -\frac{1}{d}\sum a\chi_K(a) = h$ (Davenport, Chapter 6, for the class number) and $L'/L(0, \chi_K) = -\log d + \frac{1}{h}\sum \chi_K(a)\log\Gamma(a/d)$. The character $\chi_K$ is odd and primitive, so $\xi(s) = (d/\pi)^{(s + 1)/2}\Gamma((s + 1)/2)L(s, \chi_K)$ satisfies $\xi(1 - s) = \xi(s)$ (Davenport, Chapter 9; by Chapter 2, the Gauss sum of $\chi_K$ is $i\sqrt d$, so the root number is $1$). So $\xi'/\xi(0) = -\xi'/\xi(1)$. With $\Gamma'/\Gamma(1) = -\gamma$ and $\Gamma'/\Gamma(1/2) = -\gamma - 2\log 2$ this gives
$$\frac{L'}{L}(1, \chi_K) = \gamma + \log 2\pi - \log d - \frac{L'}{L}(0, \chi_K) = \gamma + \log 2\pi - \frac{1}{h}\sum_{a = 1}^{d - 1} \chi_K(a)\log\Gamma\Bigl(\frac{a}{d}\Bigr).$$
Subtract from $\gamma$. $\square$

For $d = 7$ the class number is $1$, the residues are $1, 2, 4$, and
$$\mathrm{cs}_7 = \log\frac{\Gamma(1/7)\Gamma(2/7)\Gamma(4/7)}{\Gamma(3/7)\Gamma(5/7)\Gamma(6/7)} - \log 2\pi = 0.561580, \qquad c_1 = -1.561580.$$
Also $\mathrm{cs}_{23} = 0.999337$, with $h = 3$. The formula gives
$$\pi e^{\mathrm{cs}_d} \cdot \frac{2\pi}{\sqrt d} = \frac{\pi}{\sqrt d}\prod_{a = 1}^{d - 1} \Gamma\Bigl(\frac{a}{d}\Bigr)^{\chi_K(a)/h}.$$
This product of Gamma values is the one in the formula of Selberg and Chowla for the periods of elliptic curves with complex multiplication by $K$ (A. Selberg and S. Chowla, J. reine angew. Math. 227 (1967), 86 to 110).

### Where the constant goes

The source proves a form of the formula of Chowla and Selberg with $\mathrm{cs}_d$ in place of the Gamma values ([Lemma](/decl/New.CMLattice.chowla_selberg/)). For a prime $d$ and a CM lattice $C$ for $K$ in the sense of the source, there is a complex number $u$ with $\|\iota_p u\| = 1$ at every $p$-adic place $\iota_p : \mathbb{C} \to \mathbb{C}_p$, such that for every automorphism $\sigma$ of $\mathbb{C}$ over $K$ the lattice $C^\sigma$ satisfies
$$\operatorname{area}(C^\sigma)\, |\sigma(u)|^2 = \pi e^{\mathrm{cs}_d} \cdot \frac{2\pi}{\sqrt d}.$$
Its proof uses Kronecker's limit formula, summed over the ideal classes ([Lemma](/decl/New.CMLattice.sum_kronecker_terms/), [CM elliptic curves](/chapter/cm-elliptic-curves/)).

The data use the period $\Omega = e^{\mathrm{cs}_d} \cdot 2\pi/D_E$, where $D_E$ is the root discriminant of the number field $E$ of the data ([Definition](/decl/New.Parameters.bigOmega/)). The main prime sum is $a(\log(a/\bar w) + c_1)$, where $a$ is the number of steps and $\log\bar w$ is a mean of logarithms of weights. The archimedean size of a jet of order $a$ is $\log a! + a\log(M/\Omega)$. In the difference, $\mathrm{cs}_d$ cancels, and Stirling's formula gives
$$\log a! + a\log\frac{M}{\Omega} - a\Bigl(\log\frac{a}{\bar w} + c_1\Bigr) \leq a\Bigl(\log\bar w + \log\frac{M D_E}{2\pi}\Bigr) + 1 + \frac{\log a}{2}$$
([Lemma](/decl/New.Data.jetSize_sub_mainPrimeSum_le/)). So the argument never needs the value of $\mathrm{cs}_d$, only that the same constant appears in the period and in the prime sum. The thresholds "for large $x$" in the later chapters depend on $|\mathrm{cs}_d|$, and so on $d$ ([data and sizes](/chapter/data-and-sizes/)).

**Remark (Formalization).** The source defines $\mathrm{cs}_d$ with $\chi_K$ as the twist of the character $1$ modulo $1$, at level $1 \cdot d$, and with a real part. For odd $d$ this is the textbook constant $\gamma - L'/L(1, \chi_K)$. The form of the formula of Chowla and Selberg in the source has no Gamma values. It gives the periods up to the number $u$, and the later files take $u$ with `choose`. The source proves that $u$ is a unit at every $p$-adic place. It does not prove that $u$ is algebraic, and the notes leave open whether the argument needs this (finding F-064).
