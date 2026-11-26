---
title: The second cut-off
lean:
  - New/Reduction/OneSidedBound.lean
  - New/Reduction/Zeros/PrimeNumberTheorem.lean
  - New/Reduction/Data/AdmissibleData.lean
  - Lib/Analytic/EntireLFunction.lean
decls:
  - New.Data.primeRemainder_le
  - New.eventually_abs_primeRemainder_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The second cut-off

This section explains the step where the two editions differ most in the last part of the proof. The step turns the main inequality into the one-sided bound. The main inequality controls $R_{q_0}(x)$ only up to two values of the remainder at a second scale $x_1$. The readable edition makes these values small by the prime number theorem in progressions with an error term. The compact edition does not use this theorem. It moves $x_1$ to a good point of a long window.

### Where the second scale comes from

The data have three scales, $x \ll x_1 \ll b$. In the readable edition the scale conditions are $(\log b)^{100} \leq x$, $x^{10^6} \leq x_1$ and $x_1^{10^6} \leq b$, with $\log\log b \geq 10^{12} c$, where $c$ bounds the constants that depend on $q_0$ and $d$ only. The weight at an infinite place of $E$ is $b = a/x$ at the $b$-places and $a/x_1$ at the other places. The total remainder $\mathrm{rem}$ sums prime sums over the $a$-places. When one writes $\mathrm{rem}$ in terms of the remainders $R_q$, the value $R_{q_0}(x)$ comes with values at $x_1$ from the places of weight $a/x_1$. So the main inequality gives the following bound.

**Lemma (The bound at $x$ in terms of $x_1$).** For the data $D$,
$$R_{q_0}(x) \leq \frac{\varphi(q_0) \log^6 b}{m} + |R_{q_0}(x_1)| + \log b \cdot |R_1(x_1)|.$$

Lean: `New.Data.primeRemainder_le` (New/Reduction/OneSidedBound.lean).

*Proof.* Write $\mathrm{rem}$ through the remainders, divide the main inequality by $m a \#\Phi_b$, and use $f = \varphi(q_0)\#\Phi_a$ and $\#\Phi_a \leq \#\Phi_b \log b$, where $\Phi_a$ and $\Phi_b$ are the sets of $a$-places and $b$-places. The details are in [the main inequality and the end of the proof](/chapter/main-inequality/). $\square$

The first term is the saving. Since $m \geq \sqrt x$ and the data have $\log b = x^{\varepsilon}$, it is at most $\varphi(q_0) x^{6\varepsilon - 1/2}$. The other two terms must be smaller than $x^{-1/2}$. The factor $\log b$ in front of $R_1(x_1)$ is large, so $R_1(x_1)$ must be very small.

### The readable route: the prime number theorem

**Theorem (Prime number theorem for the remainders).** Let $d \neq 2$ be a prime, let $q \geq 1$ be prime to $d$, and let $B \in \mathbb{N}$. Then $|R_q(y)| \leq 1/(\log y)^B$ for all large $y$.

Lean: `New.eventually_abs_primeRemainder_le` (New/Reduction/Zeros/PrimeNumberTheorem.lean).

*Proof.* The source applies a Tauberian theorem to $v \mapsto R_q(e^v)$ and the function $F(s) = G_q(s)/s$, with a zero-free region and a growth bound for the L-functions. [The weighted prime remainder](/chapter/weighted-prime-remainder/) explains the proof. $\square$

The file cites Montgomery and Vaughan, *Multiplicative Number Theory I*, Corollary 11.19, a form of the Siegel–Walfisz theorem for a fixed modulus. In the readable data, $\log x_1 \geq x^{\varepsilon/12}$. With $B$ large, the theorem gives $|R_{q_0}(x_1)| \leq x^{-2}$ and $|R_1(x_1)| \leq x^{-2}$ (`New.eventually_abs_primeRemainder_exp_le`). So both terms at $x_1$ are negligible, at every admissible $x_1$.

**Remark (Formalization).** In the readable data, $x_1$ is an integer, and the field `dvd_natB` asks that $q_1 x_1$ divides $b$. The weights are the integers $b$ and $x b / x_1$. So $x_1$ is tied to $b$, and the construction of the data fixes $x_1$ before $b$. The proof cannot change $x_1$ after the data are made. This is why it needs a bound at every large $x_1$, that is, a pointwise prime number theorem.

### The compact route: a good point in a window

In the compact edition, $x_1$ is a real number. The data store only $\log x_1$, as the field `logX₁`. The weights are rounded up to multiples of $N_1$ (`Data.b₁`, `Data.b₂`), and $a$ is the least multiple of $N_1$ at least $x b$. No field other than the scale conditions mentions $x_1$. So, given data $D$ and a real $u$ that satisfies the scale conditions, the compact proof makes new data $D'$ with $\log x_1 = u$ and all else the same.

The compact identity is exact, not an inequality with absolute values. With $X = \#\mathrm{tops}/\#\mathrm{thick}$, compact `eventually_primeError_le_rpow` writes
$$R_{N_0}(x) = \frac{m \cdot \mathrm{rem}}{m \, a \, \#\mathrm{thick}} + \big(R_{N_0}(x_1) - X R_1(x_1)\big).$$
The first term is bounded by the main inequality. The second needs only a one-sided bound, and only at one $x_1$. The tool is a lemma on functions whose Laplace transform has no pole in $\operatorname{Re} s \geq 1$. Its form in the compact edition is this: if $E$ and $E'$ are polar, then for all large $t$ and every $X \in [0, e^t]$ there is $u \in [t, t^2]$ with $E(u) - X E'(u) \leq e^{-t}$. Here $E(v) = R_{N_0}(e^v)$, $E'(v) = R_1(e^v)$, $t = 10^6 \log x$, and $X \leq \log b \leq e^t$. Then $u \geq t$ gives $x^{10^6} \leq x_1$, and $u \leq t^2 = 10^{12} \log^2 x$ is far below $10^{-6}\log b = 10^{-6} x^{\varepsilon}$ for large $x$. So $u$ is an admissible value of $\log x_1$, and the second term is at most $e^{-t} = x^{-10^6}$.

### A model of the window argument

The window lemma rests on two facts. Analyticity of the transform past $\operatorname{Re} s = 1$ gives small moments at $s = 4$. A function that is large on a long window has a large moment. The following example proves a model form with explicit estimates.

**Example (The window lemma, model form).** Let $R > 3$. Let $t \geq 1$, let $A$ be a real number with $0 < A \leq e^{2t}$, and let $G : [0, \infty) \to \mathbb{R}$ be measurable with $|G(v)| \leq A e^v$ for $v \geq 0$ and
$$\Big|\int_0^\infty v^k e^{-3v} G(v)\,dv\Big| \leq \frac{k! \, A}{R^k} \quad \text{for every } k \in \mathbb{N}.$$
If $t$ is large in terms of $R$, then $G(u) \leq e^{-t}$ for some $u \in [t, t^2]$.

*Proof.* Suppose that $G(v) > e^{-t}$ for every $v \in [t, t^2]$. Let $k = \lceil t^2/9 \rceil$, so $t^2/9 \leq k \leq t^2/9 + 1$. Let $M_k = \int_0^\infty v^k e^{-3v}\,dv = k!/3^{k+1}$. Split the integral $I = \int_0^\infty v^k e^{-3v} G(v)\,dv$ at $t$ and at $t^2$.

1. The window. The density $v^k e^{-3v}/M_k$ is a gamma density with mean $\mu = (k+1)/3$ and variance $(k+1)/9$. Here $t^2/27 \leq \mu \leq t^2/27 + 1$. For $t \geq 54$ the distance from $\mu$ to the complement of $[t, t^2]$ is at least $t^2/54$. By Chebyshev's inequality, the mass outside $[t, t^2]$ is at most $\frac{(k+1)/9}{(t^2/54)^2} \leq \frac{40}{t^2}$ for large $t$, so it is at most $1/2$. So the part of $I$ on $[t, t^2]$ is at least $e^{-t} M_k / 2$.
2. The part on $[0, t)$. Here $|v^k e^{-3v} G(v)| \leq A v^k e^{-2v} \leq A t^k$. So this part is at most $A t^{k+1}$ in absolute value.
3. The part on $(t^2, \infty)$. For $v \geq t^2 \geq k$ the function $v^k e^{-v}$ decreases. So $v^k e^{-2v} \leq t^{2k} e^{-t^2} e^{-v}$, and this part is at most $A t^{2k} e^{-2t^2}$ in absolute value.

With the hypothesis on the moments,
$$\frac{e^{-t} M_k}{2} - A t^{k+1} - A t^{2k} e^{-2t^2} \leq I \leq \frac{k! \, A}{R^k}.$$
Divide by $M_k = k!/3^{k+1}$ and use $k! \geq (k/e)^k \geq (t^2/9e)^k$ and $e^{-2t^2} \leq e^{18 - 18k}$:
$$\frac{e^{-t}}{2} \leq 3A\Big[t\Big(\frac{27e}{t}\Big)^k + e^{18}\big(27e \cdot e^{-18}\big)^k + \Big(\frac{3}{R}\Big)^k\Big].$$
Since $k \geq t^2/9$, each term in the bracket is at most $e^{-c t^2}$ for large $t$, with $c > 0$ that depends on $R$. With $A \leq e^{2t}$, the right side is at most $3e^{2t} \cdot 3e^{-ct^2}$, which is less than $e^{-t}/2$ for large $t$. This is a contradiction. $\square$

In the compact proof, $G = E - X E'$ with $X \in [0, e^t]$. Compact `IsPolar.eventually_moment_le` gives, for $R > 3$ close to $3$ and large $t$, the bounds $|E(v)| \leq t e^v$ and $|\int_0^\infty v^k e^{-3v} E(v)\,dv| \leq k! \, t / R^k$, and the same for $E'$. These are Cauchy estimates for the derivatives of the transform at $s = 4$, on a circle of radius $R$ that reaches just past $\operatorname{Re} s = 1$. So $G$ satisfies the model hypotheses with $A = t(1 + X) \leq e^{2t}$. The Lean proof uses the same $k = \lceil t^2/9 \rceil$, and it writes the three estimates as the positivity of one integrand.

**Remark (Formalization).** The compact `IsPolar` (in `Lib/Analytic/Landau/PolarLandau.lean`) has one more clause than the readable `New.IsPolar`: the function $(s - 1)\Phi(s)$ is analytic on a neighbourhood of $\operatorname{Re} s \geq 1$. In Lean, $(s - 1)\Phi(s)$ at $s = 1$ is $0 \cdot \Phi(1) = 0$, whatever value $\Phi$ has there. An analytic function with value $0$ at $1$ is $(s-1)$ times an analytic function. So the clause forces $\Phi$ to be analytic at $1$, and the docstring of the compact file says so. Compact `isPolar_primeError` proves the clause for $R_M(e^v)$, with $\Phi(s) = (G_M(s)/s - \kappa)/(s - 1)$ and $\kappa = \operatorname{Re} G_M(1)$. This uses only that the L-functions have no zero on $\operatorname{Re} s \geq 1$, and that $G_M(1)$ is real.

**Remark.** The two routes use different analytic inputs. The readable route needs a zero-free region to the left of $\operatorname{Re} s = 1$ and a Tauberian theorem, and it gives a two-sided bound at every point. The compact route needs only non-vanishing on $\operatorname{Re} s \geq 1$, and it gives a one-sided bound at one point of each window. The compact `Lib/Analytic` folder has no folder for the prime number theorem. The compact file cites Pintz (1976 to 1978) and Kaczorowski (1984) on sign changes of the error terms as related work. This book has not compared the lemma with these papers.
