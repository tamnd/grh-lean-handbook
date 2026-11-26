---
title: The one-sided bound and the half-plane theorem
lean:
  - New/Reduction/OneSidedBound.lean
  - New/Reduction/Zeros/Criterion.lean
  - Statements.lean
decls:
  - New.eventually_exists_data_scales
  - New.eventually_primeRemainder_natCast_le
  - New.primeRemainder_sub_primeRemainder_floor_le
  - New.natFloor_rpow_le_two_mul_rpow
  - New.dvd_two_mul_succ_and_not_dvd_succ
  - New.eventually_primeRemainder_le_rpow
  - New.grh
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The one-sided bound and the half-plane theorem

This section puts the pieces together. It chooses data at each large integer $x$, inserts their sizes into the bound at $x$, passes from integers to real numbers, and applies Landau's criterion.

### Data with the right sizes

**Lemma (Data at every large $x$).** Let $P$ be parameters and $0 < \varepsilon < 1/100$. For all large integers $x$ there are admissible data $D$ for $P$ with

$$D.x = x, \qquad \log b \leq 2 x^{\varepsilon}, \qquad x^{1/2} \leq m, \qquad x^{\varepsilon/12} \leq \log x_1.$$

Lean: `New.eventually_exists_data_scales` (New/Reduction/OneSidedBound.lean).

*Proof.* [The data exist](/chapter/data-exist/) gives, for large $x$, data with $D.x = x$, $\log b \leq x^{\varepsilon} + 1$ and $\log x_1 \geq x^{\varepsilon/6} - 1$ (`New.eventually_exists_data`). Since $x \geq 1$, $x^\varepsilon + 1 \leq 2 x^\varepsilon$. The bound $m \geq \sqrt{x}$ is part of the data. Put $u = x^{\varepsilon/12}$. For large $x$, $u \geq 2$, so $u^2 - 1 \geq u$, that is $x^{\varepsilon/6} - 1 \geq x^{\varepsilon/12}$. $\square$

### The bound at integers

**Theorem (One-sided bound at integers).** Let $P$ be parameters with modulus $q_0$ and prime $d$, and let $0 < \varepsilon < 1/100$. For all large integers $x$,

$$R_{q_0}(x) \;\leq\; (64 \varphi(q_0) + 3) \, x^{-1/2 + 6\varepsilon}.$$

Lean: `New.eventually_primeRemainder_natCast_le` (New/Reduction/OneSidedBound.lean).

*Proof.* Take $x \geq 1$ so large that the lemma above and [the remainders at the cut-off](/decl/New.eventually_abs_primeRemainder_exp_le/) both apply. Let $D$ be the data of the lemma. Apply the bound at the cut-off with $l = \log x_1 \geq x^{\varepsilon/12}$: $|R_{q_0}(x_1)| \leq x^{-2}$ and $|R_1(x_1)| \leq x^{-2}$. [The bound at $x$](/decl/New.Data.primeRemainder_le/), with $\log b \leq 2x^\varepsilon$ and $m \geq x^{1/2}$, gives

$$R_{q_0}(x) \;\leq\; \frac{\varphi(q_0) (2x^\varepsilon)^6}{x^{1/2}} + x^{-2} + 2 x^\varepsilon x^{-2}.$$

The first term is $64 \varphi(q_0) x^{-1/2 + 6\varepsilon}$. Since $x \geq 1$ and $-2 \leq -1/2 + 6\varepsilon$, $x^{-2} \leq x^{-1/2 + 6\varepsilon}$. Since $\varepsilon - 2 \leq -1/2 + 6\varepsilon$, $x^{\varepsilon} x^{-2} \leq x^{-1/2 + 6\varepsilon}$. Add. $\square$

### From integers to real numbers

The criterion needs the bound for real $y$. The passage uses the slow variation of $R_q$.

**Lemma (Floor lemmas).** Let $d$ be a prime and $q \geq 1$. For $y \geq 2$, $R_q(y) - R_q(\lfloor y \rfloor) \leq 26/y$. For $y \geq 2$ and $-1 \leq t \leq 0$, $\lfloor y \rfloor^t \leq 2 y^t$.

Lean: `New.primeRemainder_sub_primeRemainder_floor_le`, `New.natFloor_rpow_le_two_mul_rpow` (New/Reduction/OneSidedBound.lean).

*Proof.* For $y \geq 2$, $y/2 \leq \lfloor y \rfloor \leq y$ and $y - \lfloor y \rfloor < 1$. By [slow variation](/decl/New.abs_primeRemainder_sub_le/), $R_q(y) - R_q(\lfloor y \rfloor) \leq 13 (y - \lfloor y \rfloor)/\lfloor y \rfloor \leq 13/(y/2)$. For the second claim, $t \leq 0$ gives $\lfloor y \rfloor^t \leq (y/2)^t = 2^{-t} y^t \leq 2 y^t$, since $-t \leq 1$. $\square$

**Lemma (The congruence of the parameters).** Let $q_0 > 0$ be even and $d \equiv q_0/2 - 1 \pmod{q_0}$. Then $q_0 \mid 2(d + 1)$ and $q_0 \nmid d + 1$.

Lean: `New.dvd_two_mul_succ_and_not_dvd_succ` (New/Reduction/OneSidedBound.lean).

*Proof.* Write $q_0 = 2q$. Then $d + 1 \equiv q \pmod{2q}$. So $2(d + 1) \equiv 2q \equiv 0$, and $d + 1 \equiv q \not\equiv 0$, since $0 < q < 2q$. $\square$

This is the form in which the structure of parameters stores the congruence.

**Theorem (One-sided bound).** Let $q_0 > 0$ be a multiple of $18480$, let $d$ be a prime with $d \equiv q_0/2 - 1 \pmod{q_0}$, and let $\varepsilon > 0$. Then

$$R_{q_0}(y) \;\leq\; y^{-1/2 + \varepsilon}$$

for all large real $y$.

Lean: `New.eventually_primeRemainder_le_rpow` (New/Reduction/OneSidedBound.lean).

*Proof.* The numbers $q_0$ and $d$, with the lemma above, form parameters $P$. Put $\delta = \min(1/200, \varepsilon/7)$. Then $0 < \delta < 1/100$ and $7\delta \leq \varepsilon$. Put $t = -1/2 + 6\delta$ and $C = 64\varphi(q_0) + 3$. Then $-1 \leq t \leq 0$. For large real $y$, three things hold: $y \geq 2$; the bound at integers, with $\delta$ in place of $\varepsilon$, holds at $\lfloor y \rfloor$; and $y^\delta \geq 2C + 26$. For such $y$,

$$R_{q_0}(y) \;\leq\; R_{q_0}(\lfloor y \rfloor) + 26 y^{-1} \;\leq\; C \lfloor y \rfloor^t + 26 y^{-1} \;\leq\; 2C y^t + 26 y^t \;\leq\; y^\delta y^t \;=\; y^{-1/2 + 7\delta} \;\leq\; y^{-1/2 + \varepsilon}.$$

Here $y^{-1} \leq y^t$ since $t \geq -1$ and $y \geq 1$. $\square$

**Example.** Take $q = 1$, so $q_0 = 18480$ and $\varphi(q_0) = 3840$. The constant of the bound at integers is $C = 64 \cdot 3840 + 3 = 245763$. The class $q_0/2 - 1 = 9239$ contains the primes $9239$, $46199$, $64679$, $138599$, and so on (each is $9239 + 18480 k$; for example $27719 = 53 \cdot 523$ is not prime). For $\varepsilon = 1/10$, $\delta = 1/200$, and the proof needs $y^{1/200} \geq 2C + 26 = 491552$, that is $y \geq 491552^{200} \approx 10^{1138}$. The other thresholds are not explicit.

### The half-plane theorem

**Theorem (Recalled: Landau's criterion, one-sided form).** Let $q_0 > 0$ be a multiple of $8$, let $d_0$ be prime to $q_0$ with $d_0 \equiv 7 \pmod 8$, and let $\beta > 1/2$. Suppose that for every prime $d \equiv d_0 \pmod{q_0}$, $R^{(d)}_{q_0}(y) \leq y^{\beta - 1}$ for all large real $y$. Then $L(\rho, \psi) \neq 0$ for every Dirichlet character $\psi$ modulo $q_0$ and every $\rho \neq 1$ with $\operatorname{Re} \rho > \beta$.

Lean: `New.LFunction_ne_zero_of_primeRemainder_le` (New/Reduction/Zeros/Criterion.lean).

[Landau's criterion](/chapter/landau-criterion/) proves it. The proof uses one prime $d$ of the class, chosen so that no $L(s, \psi \chi_K)$ vanishes in $\operatorname{Re} s \geq \beta$, $|\operatorname{Im} s| \leq |\operatorname{Im} \rho|$ (`New.exists_entireL_quadTwist_ne_zero`, a zero density argument, which needs $\beta > 1/2$). Then the transform of $v \mapsto R_{q_0}(e^v)$ has residues $n(s)/(\varphi(q_0) s(1 - s))$ there, with $n(s)$ the number of zeros of the $L(s, \psi)$ at $s$, and Landau's lemma on Laplace transforms of functions bounded on one side shows $n(\rho) = 0$.

**Theorem (The half-plane theorem).** For every $q \geq 1$, every Dirichlet character $\chi$ modulo $q$ and every $s$ with $\operatorname{Re} s > 1/2$ and ($\chi \neq 1$ or $s \neq 1$), $L(s, \chi) \neq 0$.

Lean: `New.grh` (New/Reduction/OneSidedBound.lean).

The statement is the proposition `DirichletLNonvanishingRightOfHalf` of Statements.lean. Here $L(s, \chi)$ is `DirichletCharacter.LFunction` (Mathlib), the analytic continuation of $\sum \chi(n) n^{-s}$.

*Proof.* Let $q$, $\chi$ and $\rho$ be given, with $\operatorname{Re} \rho > 1/2$ and ($\chi \neq 1$ or $\rho \neq 1$).

*The case $\rho = 1$.* Then $\chi \neq 1$, and $L(1, \chi) \neq 0$ by Dirichlet's theorem (`DirichletCharacter.LFunction_ne_zero_of_one_le_re` (Mathlib)).

*The case $\rho \neq 1$.* Choose $\beta$ with $1/2 < \beta < \operatorname{Re} \rho$. Put $q_0 = 18480 q$ and $d_0 = 9240 q - 1$, so $q_0 = 2(d_0 + 1)$ and $d_0 = q_0/2 - 1$. The number $d_0$ is odd. A common prime factor of $d_0$ and $2(d_0 + 1)$ divides $2$ or divides both $d_0$ and $d_0 + 1$, so $d_0$ is prime to $q_0$. Since $9240 = 8 \cdot 1155$, $d_0 \equiv -1 \equiv 7 \pmod 8$. Also $8 \mid q_0$.

For every prime $d \equiv d_0 \pmod{q_0}$, the one-sided bound with $\varepsilon = \beta - 1/2 > 0$ gives $R^{(d)}_{q_0}(y) \leq y^{-1/2 + (\beta - 1/2)} = y^{\beta - 1}$ for all large $y$. So the criterion applies to the character $\chi'$ modulo $q_0$ induced by $\chi$ (`DirichletCharacter.changeLevel` (Mathlib)), and $L(\rho, \chi') \neq 0$.

The induced character differs from $\chi$ only at the primes $p \mid q_0$, $p \nmid q$. For $\chi \neq 1$ or $\rho \neq 1$, Mathlib gives

$$L(\rho, \chi') \;=\; L(\rho, \chi) \prod_{p \mid q_0} \big( 1 - \chi(p) p^{-\rho} \big)$$

(`DirichletCharacter.LFunction_changeLevel` (Mathlib)). A product $uv$ that is nonzero has $u \neq 0$. So $L(\rho, \chi) \neq 0$. $\square$

**Remark.** The last step does not need that the Euler factors are nonzero. It uses only that a nonzero product has nonzero factors.

**Remark.** The criterion asks the bound for every prime $d$ of the class, with a threshold that may depend on $d$, and then uses one $d$ only. So the method never needs a bound that is uniform in $d$.

**Remark (Formalization).** The source states `New.grh` in terms of the Mathlib $L$-function `DirichletCharacter.LFunction`, so the statement does not depend on the definitions of the source. [From the half-plane to the line](/chapter/half-plane-to-line/) deduces the other four statements of Statements.lean from it. Lean accepts `New.grh`, if the checks that the source reports hold. The book does not claim more.
