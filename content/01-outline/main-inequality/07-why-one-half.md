---
title: Why the exponent is one half
lean:
  - New/Reduction/OneSidedBound.lean
  - New/Reduction/Data/Existence.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Why the exponent is one half

The half-plane theorem has the exponent $1/2$. A reader should ask where this number enters the proof. The answer is short: it enters at one place, the number $m$ of theta lifts, and at one more place in the criterion. This section traces both, and says what is open.

### The exponent comes from m

Follow the exponents through Sections 3 to 6. The main inequality is $m \cdot \mathrm{rem} \leq f a \log^5 b$. Division by $m a \#\Phi_b$ gives the first term $\varphi(q_0) \log^6 b / m$ of the bound at $x$. The other terms are at most $x^{-2}(1 + 2x^{\varepsilon})$. So

$$R_{q_0}(x) \;\leq\; \frac{\varphi(q_0) \log^6 b}{m} + O(x^{-2 + \varepsilon}).$$

The data have $\log b \approx x^{\varepsilon}$, with $\varepsilon$ as small as we like. So the factor $\log^6 b$ costs only $x^{6\varepsilon}$. The factor $1/m$ is the saving. The data of [the data exist](/chapter/data-exist/) take $m$ to be the least power of $2$ with $m \geq \sqrt{x}$. So the saving is $x^{-1/2}$, and the exponent of the one-sided bound is $-1/2 + 6\varepsilon$.

Suppose, as a thought experiment, that the data had $m \geq x^\theta$ for some $\theta$, with all other bounds unchanged. The same proof would give $R_{q_0}(y) \leq y^{-\theta + \varepsilon}$ for large $y$, and the criterion, if it applied with $\beta = 1 - \theta$, would give $L(s, \psi) \neq 0$ in $\operatorname{Re} s > 1 - \theta$. For $\theta < 1/2$ this is a weaker theorem. For $\theta > 1/2$ it is false. The principal character $\psi_0$ modulo $q_0$ has $L(s, \psi_0) = \zeta(s) \prod_{p \mid q_0} (1 - p^{-s})$, so $L(s, \psi_0)$ vanishes at every zero of $\zeta$. Hardy proved in 1914 that $\zeta$ has infinitely many zeros on the line $\operatorname{Re} s = 1/2$. So no correct form of the method can have $\theta > 1/2$. The value $\theta = 1/2$ is the largest one that is consistent with the known zeros.

The size of the bound also matches the expected truth. If GRH holds, the explicit formula writes $R_{q_0}(y)$ as a sum over the zeros $\rho$ of the $L(s, \psi)$ and $L(s, \psi \chi_K)$, with terms of size $y^{\operatorname{Re} \rho - 1}/|\rho|^2$. With $\operatorname{Re} \rho = 1/2$ these are of size $y^{-1/2}$. So the one-sided bound $R_{q_0}(y) \leq y^{-1/2 + \varepsilon}$ is of the true order, up to $y^{\varepsilon}$. This is a heuristic only. The source uses no explicit formula.

### Where m is fixed

The number $m$ enters the data in several conditions. The ones that tie $m$ to $x$ are these.

- $\sqrt{x} \leq m \leq 2\sqrt{x}$, and $m$ is a power of $2$.
- $2^s = m^{22}$, and the field $E = K(\zeta_{q_1})$ has $q_1 = q_0 \cdot \operatorname{towerDeg}(s)$. So the degree of $E$ is about $m^{22} \approx x^{11}$. The compact edition records $\#\Phi_a \in [x^{11}, x^{11} (\log b)^{1/5}]$.
- The ranks satisfy $r \in [x^5, 3x^5]$ and $k = r + 1 - m$. So $m$ is much smaller than $r$.
- The level $N$ has $\log N \in [m \log b, 30 m \log b]$: it pays for the excesses of the $m$ lifts.
- Theorem C uses $2 m^2 t x_1 \leq b$, where $t = 5r$ is the step of the ranks. Since $m \leq r \leq 3x^5$ and $b \geq x_1^{10^6}$, this condition holds with a large margin, and it does not force $m \leq 2\sqrt{x}$.

The source does not say which of these conditions forces $m \leq 2\sqrt{x}$, or whether a larger $m$ breaks the argument at a definite place. The research note for this volume records the question (research note b, Section 10, question 1), and the register of findings lists it as open question Q-10. The argument above shows that some condition must fail for $m \geq x^{\theta}$ with $\theta > 1/2$, if the rest of the proof is correct. The book does not answer the question.

### The criterion needs one half too

The exponent $1/2$ enters a second time, in the criterion. [Landau's criterion](/chapter/landau-criterion/) needs $\beta > 1/2$. The reason is the choice of one prime $d$ in the class $d_0 \bmod q_0$ such that no $L(s, \psi \chi_K)$ vanishes in $\operatorname{Re} s \geq \beta$, $|\operatorname{Im} s| \leq T$. The source proves that such $d$ exist by a zero density argument for the family of quadratic twists (`New.exists_entireL_quadTwist_ne_zero`, in Lib/Analytic/QuadraticTwist.lean). Zero density estimates of this kind say that few twists have a zero in a box to the right of $1/2$. They say nothing on the line $\operatorname{Re} s = 1/2$. So the criterion is stated for $\beta > 1/2$ only.

The two appearances of $1/2$ are independent. The first is a property of the algebraic method: the saving $1/m$. The second is a property of the analytic family: zero density for twists. They give the same threshold. Landau's lemma itself, the last step of the criterion, needs only $\beta > 0$.

### The other errors

Every other loss is either a power of $\log b$, which is $x^{O(\varepsilon)}$, or at most $O(x^{-1})$: the terms at $x_1$ are $O(x^{-2+\varepsilon})$, and any power of $x$ is possible there with a larger $B$; the passage from integers to real numbers costs $26/y$. So $1/m$ is the only loss that fixes the exponent.
