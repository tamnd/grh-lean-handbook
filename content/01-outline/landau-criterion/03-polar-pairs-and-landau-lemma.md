---
title: Polar pairs and Landau's lemma
lean:
  - Lib/Analytic/EntireLFunction.lean
  - Lib/Analytic/Landau.lean
decls:
  - New.IsPolar
  - New.exists_measure_laplace_eq
  - New.exists_Ioi_subset_integrableExpSet_of_analyticAt
  - New.exists_Ioi_subset_integrableExpSet
  - New.IsPolar.landau
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Polar pairs and Landau's lemma

This section proves the form of Landau's theorem that the criterion uses. The source packages the explicit formula in one notion, a polar pair: a function $E$ and a function $r$ that gives the residues of the transform of $E$. A one-sided bound $E(v) \leq e^{(\beta - 1)v}$, and residues of real part $\geq 0$ at the real points to the right of $\beta$, give residue $0$ at every point to the right of $\beta$. The proof is the proof of the model criterion of Section 2, with the zeta function taken out.

### Polar pairs

In the model case the function was $E(v) = R(e^v)$. The substitution $y = e^v$ turns the Mellin transform $\int_1^\infty R(y) y^{-s}\, dy$ into the Laplace transform $\int_0^\infty E(v) e^{(1 - s)v}\, dv$. The source uses the second form.

**Definition (Polar pair).** Let $E : \mathbb{R} \to \mathbb{R}$ and $r : \mathbb{C} \to \mathbb{C}$. The pair $(E, r)$ is *polar* if $E$ is measurable and there are a real number $C$ and a function $\Phi : \mathbb{C} \to \mathbb{C}$, meromorphic on $\mathbb{C}$, with these three properties.

1. $|E(v)| \leq C e^v$ for every $v \geq 0$.
2. $\Phi(s) = \int_0^\infty E(v)\, e^{(1 - s)v}\, dv$ for every $s$ with $\operatorname{Re} s > 2$.
3. For every $\rho$ with $\operatorname{Re} \rho > 0$, $(z - \rho)\Phi(z) \to r(\rho)$ as $z \to \rho$, $z \neq \rho$.

Lean: `New.IsPolar` (Lib/Analytic/EntireLFunction.lean).

Property 1 makes the integral in property 2 converge absolutely, and by the identity theorem property 2 fixes $\Phi$ off its poles. Property 3 says that $\Phi$ has at most simple poles in the half-plane $\operatorname{Re} s > 0$, and that $r(\rho)$ is the residue at $\rho$. At a point $\rho$ where $\Phi$ is analytic, the limit is $0$, so $r(\rho) = 0$. So in the half-plane $\operatorname{Re} s > 0$ the function $r$ is determined by $E$. In $\operatorname{Re} s \leq 0$ the definition puts no condition on $r$.

**Example (The model pair).** Let $R$ be the remainder of Section 2 and let $Z(s) = (s - 1)\zeta(s)$. Step 1 and Step 2 of the proof of the model criterion show that $(v \mapsto R(e^v), r)$ is a polar pair for
$$r(s) = \frac{\operatorname{ord}_s Z}{s(1 - s)}.$$
At $s = 1$ the formula reads $0/0$. With the convention $x/0 = 0$ of Lean it gives $r(1) = 0$, which is the right value, since the transform has no pole at $1$.

**Remark (Formalization).** A polar pair is not a notion of the textbooks. It packages the continuation of one transform, its simple poles in the right half-plane, and a name $r$ for the residues. The definition asks $\Phi$ to be meromorphic on all of $\mathbb{C}$, while the proof of the next theorem uses only $\operatorname{Re} s > 0$. The integral in property 2 is a Bochner integral. Lean gives such an integral the value $0$ if the integrand is not integrable, but property 1 makes the integrand integrable, so the junk value does not occur.

### The positive measure

The first step is the measure of Step 3 of the model proof.

**Lemma (The positive measure).** Let $E$ be measurable with $|E(v)| \leq C e^v$ for $v \geq 0$. Let $\beta > 0$, and suppose that $E(v) \leq e^{(\beta - 1)v}$ for all large $v$. Then there are a measure $\mu$ on $\mathbb{R}$ and a real number $K$ such that, for every $s$ with $\operatorname{Re} s > \beta + 2$, the function $e^{-(\operatorname{Re} s)|v|}$ is $\mu$-integrable and
$$\int_{\mathbb{R}} e^{-s|v|}\, d\mu(v) = \frac{K}{s - \beta} - \int_0^\infty E(v)\, e^{(1 - s)v}\, dv.$$

Lean: `New.exists_measure_laplace_eq` (Lib/Analytic/Landau.lean), with `New.exists_mul_exp_le` (Lib/Analytic/Landau.lean) for the constant $K$.

*Proof.* Let $Y \geq 0$ be such that $E(v) \leq e^{(\beta - 1)v}$ for $v \geq Y$. Put $K = \max(1, |C| e^{2Y})$. We claim that $E(v) e^v \leq K e^{\beta v}$ for every $v > 0$. For $v \geq Y$ we have $E(v) e^v \leq e^{\beta v} \leq K e^{\beta v}$. For $0 < v \leq Y$ we have $E(v) e^v \leq |C| e^{2v} \leq |C| e^{2Y} \leq K \leq K e^{\beta v}$, since $\beta v \geq 0$. Here $\beta > 0$ is used. Let $\mu$ be the measure on $(0, \infty)$ with the density $K e^{\beta v} - E(v) e^v \geq 0$ with respect to $dv$. For $\operatorname{Re} s > \beta + 2$ both $K e^{(\beta - s)v}$ and $E(v) e^{(1 - s)v}$ are integrable on $(0, \infty)$, and
$$\int e^{-sv}\, d\mu(v) = K\int_0^\infty e^{(\beta - s)v}\, dv - \int_0^\infty E(v)\, e^{(1 - s)v}\, dv = \frac{K}{s - \beta} - \int_0^\infty E(v)\, e^{(1 - s)v}\, dv.$$
On $(0, \infty)$ we have $e^{-sv} = e^{-s|v|}$. $\square$

The measure $\mu$ is the place where the one-sided bound becomes a positivity. Only an upper bound for $E$ enters. The object with one sign is the density $K e^{\beta v} - E(v)e^v$, not the weights $\lambda(n)$.

### Landau's lemma in the form of the source

The source writes the transform of $\mu$ as a moment generating function: $\int e^{sX}\, d\mu$ with $X(v) = -|v| \leq 0$. For a measure on $\mathbb{R}$ and a function $X$, let $S$ be the set of real $t$ for which $e^{tX}$ is $\mu$-integrable, and let $M(s) = \int e^{sX}\, d\mu$ for complex $s$. If $X \leq 0$, then $S$ is a half-line that is unbounded to the right.

**Lemma (Landau's lemma).** Let $\mu$ be a measure on $\mathbb{R}$, let $X : \mathbb{R} \to \mathbb{R}$ be measurable with $X \leq 0$, and let $a \in \mathbb{R}$ be such that every $t > a$ lies in the interior of $S$. Let $g$ be analytic at $a$. Suppose that for every real $x > a$ close enough to $a$, the functions $g$ and $M$ are equal on a neighbourhood of $x$. Then there is $b < a$ such that every $t > b$ lies in $S$.

Lean: `New.exists_Ioi_subset_integrableExpSet_of_analyticAt` (Lib/Analytic/Landau.lean), with `New.mem_integrableExpSet_of_summable_taylor` (Lib/Analytic/Landau.lean) for the series.

*Proof.* This is the proof of Landau's theorem in [the model case](/chapter/landau-criterion/#the-model-case), at a point $z$ near $a$. Let $g$ be analytic on the disc $|s - a| < \varepsilon$. Choose a real $z$ with $a < z < a + \varepsilon/2$ at which $g = M$ near $z$. The Taylor series of $g$ at $z$ converges on the disc $|s - z| < \varepsilon/2$, which lies in the disc of $g$. Its coefficients are $M^{(k)}(z)/k! = \int X^k e^{zX}\, d\mu / k!$. For real $\sigma$ with $z - \varepsilon/2 < \sigma \leq a$, each term $(\sigma - z)^k X^k e^{zX}/k!$ is $\geq 0$, as $\sigma - z \leq 0$ and $X \leq 0$. By Tonelli, the sum of the integrals of the terms is the integral of $e^{\sigma X}$, and it is finite. So $\sigma \in S$. Take $b = z - \varepsilon/2$. $\square$

**Lemma (A residue of real part at most zero).** Let $\mu$, $X$ and $a$ be as in the previous lemma. Let $\Psi$ be meromorphic at $a$ and equal to $M$ on a punctured neighbourhood of every real $x > a$. Suppose that $(z - a)\Psi(z) \to c$ as $z \to a$, $z \neq a$, with $\operatorname{Re} c \leq 0$. Then there is $b < a$ such that every $t > b$ lies in $S$.

Lean: `New.exists_Ioi_subset_integrableExpSet` (Lib/Analytic/Landau.lean).

*Proof.* For real $x > a$ near $a$ the function $\Psi$ is analytic at $x$ and equal to $M$ near $x$. So $(x - a)\Psi(x) = (x - a)M(x) \geq 0$, since $M(x) = \int e^{xX}\, d\mu \geq 0$. The limit gives $c \geq 0$, so $c$ is real and $c \geq 0$, and with $\operatorname{Re} c \leq 0$ we get $c = 0$. Then $(z - a)\Psi(z)$ extends to an analytic function $G$ at $a$ with $G(a) = 0$, and $g(z) = G(z)/(z - a)$ is analytic at $a$ and equal to $\Psi$ off $a$. The previous lemma applies to $g$. $\square$

### The theorem

**Theorem (Landau's lemma for polar pairs).** Let $(E, r)$ be a polar pair and let $\beta > 0$. Suppose that $\operatorname{Re} r(x) \geq 0$ for every real $x > \beta$, and that $E(v) \leq e^{(\beta - 1)v}$ for all large $v$. Then $r(\rho) = 0$ for every $\rho \in \mathbb{C}$ with $\operatorname{Re} \rho > \beta$.

Lean: `New.IsPolar.landau` (Lib/Analytic/Landau.lean).

*Proof.* Let $C$ and $\Phi$ be as in the definition. By [Lemma](/decl/New.exists_measure_laplace_eq/), there are $\mu$ and $K$ such that $F(s) = \int e^{-s|v|}\, d\mu$ converges and equals $\Psi(s) := K/(s - \beta) - \Phi(s)$ for $\operatorname{Re} s > \beta + 2$. Let $S$ be the set of real $t$ at which $F$ converges absolutely. It contains $(\beta + 2, \infty)$, so its complement is bounded above.

Step 1: the residues of $\Psi$. Let $\operatorname{Re} \rho > \beta$. Then $\operatorname{Re} \rho > 0$, so $(z - \rho)\Phi(z) \to r(\rho)$ by property 3. The function $K/(s - \beta)$ is continuous at $\rho$, since $\rho \neq \beta$. So $(z - \rho)\Psi(z) \to -r(\rho)$.

Step 2: the point $a$. Let $a$ be the least upper bound of $\{\beta\} \cup (\mathbb{R} \setminus S)$. So $a = \max(\beta, \sigma_c)$, where $\sigma_c$ is the abscissa of convergence. Every $t > a$ is in $S$, and $(a, \infty)$ is open, so it lies in the interior of $S$. So $F$ is analytic on $\operatorname{Re} s > a$. The functions $\Psi$ and $F$ are meromorphic on the connected half-plane $\operatorname{Re} s > a$, and they are equal on $\operatorname{Re} s > \beta + 2$. By the identity theorem they are equal on a punctured neighbourhood of every point of $\operatorname{Re} s > a$.

Step 3: $a = \beta$. Suppose $a > \beta$. Then $a$ is real and $a > \beta$, so $\operatorname{Re}(-r(a)) \leq 0$ by the hypothesis on $r$. By Step 1, $(z - a)\Psi(z) \to -r(a)$. By [Lemma](/decl/New.exists_Ioi_subset_integrableExpSet/), with $X(v) = -|v|$, there is $b < a$ with $(b, \infty) \subset S$. By the definition of $a$ as a least upper bound, there is $\sigma \notin S$ with $\max(\beta, b) < \sigma \leq a$. This is a contradiction.

Step 4: the residue at $\rho$. So $a = \beta$, and $F$ is analytic at every $\rho$ with $\operatorname{Re} \rho > \beta$. Then $(z - \rho)F(z) \to 0$. Since $\Psi = F$ on a punctured neighbourhood of $\rho$, Step 1 gives $-r(\rho) = 0$. $\square$

The proof uses the hypothesis on $r$ at one real point only, the point $a$. But this point is not known in advance, so the theorem asks the sign at every real point to the right of $\beta$.

**Remark (Formalization).** The theorem asks only $\beta > 0$. It is used twice. First, property 3 of a polar pair gives the residues only in $\operatorname{Re} s > 0$, and Step 1 needs them at points to the right of $\beta$. Second, the constant $K$ of the lemma needs $e^{\beta v} \geq 1$ for $v > 0$. The criterion of Section 5 has $\beta > 1/2$, and it passes $\beta > 0$ to this theorem by linear arithmetic. The condition $\beta > 1/2$ is used only for the choice of the prime $d$. The theorem bounds $E$ from above only, and it asks only the real part of $r$ at real points. In the application $r$ is real at real points.
