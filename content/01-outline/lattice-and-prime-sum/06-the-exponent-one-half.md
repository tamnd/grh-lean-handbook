---
title: Why the result stops at the exponent one half
lean:
  - New/Reduction/OneSidedBound.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Why the result stops at the exponent one half

This section follows the main inequality to the one-sided bound $R_{q_0}(x) \leq x^{-1/2 + \varepsilon}$. It shows that the exponent $-1/2$ is the saving $1/m$ with $m \approx \sqrt x$. Then it explains why the source needs no larger saving and why no method can give one. The full proofs are in [the main inequality and the end of the proof](/chapter/main-inequality/).

### From the main inequality to the remainder

The main inequality gives $\operatorname{rem} \leq f a\log^5 b / m$. The identity for the total remainder ([Theorem](/decl/New.Data.totalRemainder_eq/)) gives
$$R_{q_0}(x) = \frac{\operatorname{rem}}{a\,\#\Phi_b} + R_{q_0}(x_1) - \frac{\#\Phi_a}{\#\Phi_b}\, R_1(x_1).$$
Two facts of the data finish the computation. The field has $f = \varphi(q_0)\,\#\Phi_a$ infinite places, and the $b$-places are not too few: $\#\Phi_a \leq \#\Phi_b \log b$ ([the data and its sizes](/chapter/data-and-sizes/)). So
$$\frac{\operatorname{rem}}{a\,\#\Phi_b} \leq \frac{\varphi(q_0)\,\#\Phi_a \log^5 b}{m\,\#\Phi_b} \leq \frac{\varphi(q_0)\log^6 b}{m}.$$
This is the lemma `New.Data.primeRemainder_le` of New/Reduction/OneSidedBound.lean. For data $D$ for the parameters $P$,
$$R_{q_0}(x) \leq \frac{\varphi(q_0)\log^6 b}{m} + |R_{q_0}(x_1)| + \log b \cdot |R_1(x_1)| .$$
Here $R_q$ is [the weighted prime remainder](/chapter/weighted-prime-remainder/) of the prime $d$ and the modulus $q$.

The first term is the saving. The other two are values at the second cut-off $x_1$, which is enormous. The source chooses the data so that both are negligible.

1. For each $0 < \varepsilon < 1/100$ and every large integer $x$, there are data whose first scale is $x$, with $\log b \leq 2x^\varepsilon$, $\sqrt x \leq m$ and $x^{\varepsilon/12} \leq \log x_1$ (`New.eventually_exists_data_scales`).
2. The prime number theorem with a saving of a power of $\log y$, at $y = x_1$, gives $|R_{q_0}(x_1)| \leq x^{-2}$ and $|R_1(x_1)| \leq x^{-2}$ (`New.eventually_abs_primeRemainder_exp_le`).

With these, the bound becomes
$$R_{q_0}(x) \leq \frac{\varphi(q_0)(2x^\varepsilon)^6}{\sqrt x} + x^{-2} + 2x^{\varepsilon} x^{-2} \leq (64\,\varphi(q_0) + 3)\, x^{-1/2 + 6\varepsilon}$$
for all large integers $x$. A short argument passes from integers to real $y$, and a change of $\varepsilon$ removes the constant. The result is [Theorem](/decl/New.eventually_primeRemainder_le_rpow/): $R_{q_0}(y) \leq y^{-1/2+\varepsilon}$ for all large real $y$.

So the exponent $-1/2$ comes from one place: the factor $1/m$, with $m \geq \sqrt x$. The factor $\log^6 b$ costs only $x^{6\varepsilon}$, because $\log b$ is a small power of $x$. The second cut-off costs nothing, because the prime number theorem is strong enough at $x_1$.

### A thought experiment

Suppose that data existed with $m \approx x^\theta$ for some $\theta > 1/2$, and that every size comparison of the source still held. Then the same computation would give
$$R_{q_0}(x) \ll x^{-\theta + 6\varepsilon},$$
and a criterion of Landau's type would give a zero-free half-plane $\operatorname{Re} s > 1 - \theta$, to the left of the critical line.

### Why the source needs no more

The criterion of [Landau's criterion](/chapter/landau-criterion/) takes a bound $R_{q_0}(x) \leq x^{\beta - 1}$ with $\beta > 1/2$, for every prime $d$ of a residue class, and gives $L(\rho, \psi) \neq 0$ for $\operatorname{Re}\rho > \beta$. Its proof uses $\beta > 1/2$, through a zero density estimate for quadratic twists. The main theorem asks for every $\beta > 1/2$. So the exponent $-1/2 + \varepsilon$ for every $\varepsilon > 0$ is exactly what the end of the proof needs, and $m \approx \sqrt x$ is exactly enough.

### Why no method can give more

In the model case of the zeta function, a one-sided bound $R(x) \leq x^{\beta - 1}$ for all large $x$, with $0 < \beta < 1$, gives $\zeta(s) \neq 0$ for $\operatorname{Re} s > \beta$ ([the model case](/chapter/landau-criterion/#the-model-case)). But $\zeta$ has infinitely many zeros on the line $\operatorname{Re} s = 1/2$, by a theorem of Hardy (1914); see Titchmarsh, *The Theory of the Riemann Zeta-Function*, Chapter X. So in the model the bound fails for every $\beta < 1/2$. The model remainder cannot be $O(x^{-\theta})$ for any $\theta > 1/2$.

The remainder of the source is built from the L-functions $L(s, \xi\chi_K)$ in the same way ([Landau's criterion](/chapter/landau-criterion/)). One expects the same obstruction for it, because these L-functions also have zeros on the critical line. Neither the source nor this book proves this. Under this expectation, the saving $1/m$ cannot be better than $x^{-1/2}$ for any choice of data that satisfies all the comparisons. So some step of the method must fail for $m \gg \sqrt x$.

### Where $m$ is tied to $x$

The source does not say which of its comparisons would fail for a larger $m$. This is an open question of the research notes of this book (research note b, §10, question 1). Here is what the source shows.

1. The bound $m \leq 2\sqrt x$ is a field of the data (`New.Data.m_mem`). It is used only in the size comparisons: through $x \leq m^2 \leq 4x$ (`New.Data.m_sq_mem_Icc`) and through the instance of the automation for sizes that treats $m$ as a quantity of degree $1/2$ in $x$ (New/Reduction/Data/Magnitudes.lean).
2. The field grows with $m$. The data have $2^s = m^{22}$ and $E = E(s)$, so $f \geq 2^s = m^{22} \geq x^{11}$, and the bound $q_1 \leq x^{12}$ uses $2^s = m^{22} \leq 2^{22} x^{11}$ ([the data and its sizes](/chapter/data-and-sizes/)). A larger $m$ makes the field larger and changes every size that depends on $f$ or $q_1$.
3. Some constraints that contain $m$ are far from binding: Theorem C uses $2m^2\, t\, x_1 \leq b$, and the left side is at most $120\, x^6 x_1 \leq x_1^2$.
4. The ranks $r \approx x^5$ and $k = r + 1 - m$ leave room for $m$ up to almost $x^5$.

None of these facts alone explains the exponent $1/2$. If the expectation of the previous subsection is right, and Lean accepts the source as reported, then some comparison of the source fails for $m \gg \sqrt x$: otherwise the same proof, with a larger $m$, would give a false statement. Exercise 5 asks for a first step.

### One side only

The bound $R_{q_0}(x) \leq x^{-1/2+\varepsilon}$ has one side. The main inequality bounds $m\operatorname{rem}$ from above, because a large positive remainder makes the forms of Theorem A too short (Section 5). A large negative remainder makes the forms longer, and nothing forbids long forms. [Landau's criterion](/chapter/landau-criterion/) needs only this side, because of the positivity in Landau's theorem.
