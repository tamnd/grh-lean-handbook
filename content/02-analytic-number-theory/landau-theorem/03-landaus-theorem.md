---
title: Landau's theorem
lean:
  - Lib/Analytic/Landau.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Landau's theorem

This section states and proves Landau's theorem in the classical forms: for Laplace transforms of positive measures, for Dirichlet series with nonnegative coefficients, and for Mellin integrals of functions that are eventually nonnegative. All of them follow from one local statement: if the transform continues analytically to a disc of radius $\varepsilon$ about a real point $a$, and converges to the right of $a$, then it converges to the right of $a - \varepsilon$. The section ends with the form that the applications use: a transform that continues along the real axis converges as far as it continues.

### The local theorem

Volume 1 proves Landau's theorem with a loss: from a disc of radius $\varepsilon$ about the abscissa it gets convergence on a segment of length $\varepsilon/6$ ([The model case](/chapter/landau-criterion/#the-model-case)). The same argument gives the whole radius, and this sharp form is the one that gives the corollaries below.

**Theorem (Landau, local form).** Let $\mu$ be a positive Borel measure on $[0, \infty)$, and let $a$ be real with $F(\sigma) < \infty$ for every $\sigma > a$. Let $\varepsilon > 0$, and let $g$ be analytic on the disc $D = \{s : |s - a| < \varepsilon\}$ with $g(s) = F(s)$ for $s \in D$ with $\operatorname{Re} s > a$. Then $F(\sigma) < \infty$ for every $\sigma > a - \varepsilon$.

*Proof.* Step 1: one analytic function. Let $H = \{s : \operatorname{Re} s > a\}$. By the proposition on [the analyticity of the transform](/chapter/landau-theorem/#abscissae-of-convergence) in Section 2, $F$ is analytic on $H$. The set $D \cap H$ is convex, so connected, and $g = F$ on it. So the function $h$ equal to $g$ on $D$ and to $F$ on $H$ is well defined and analytic on the open set $D \cup H$.

Step 2: a large disc at a point to the right. Fix $\delta$ with $0 < \delta < \varepsilon$, and put $z = a + \delta$. We claim that the disc $D' = \{s : |s - z| < \varepsilon\}$ lies in $D \cup H$. Let $s = z + w$ with $|w| < \varepsilon$ and $\operatorname{Re} s \leq a$, so $\operatorname{Re} w \leq -\delta$. Then
$$|s - a|^2 = (\delta + \operatorname{Re} w)^2 + (\operatorname{Im} w)^2 = \delta^2 + 2\delta \operatorname{Re} w + |w|^2 \leq -\delta^2 + |w|^2 < \varepsilon^2,$$
so $s \in D$. This proves the claim. By the theorem of Cauchy and Taylor, the Taylor series of $h$ at $z$ converges to $h$ on $D'$.

Step 3: the sum of the series. Let $\sigma$ be real with $z - \varepsilon < \sigma < z$. Near $z$ we have $h = F$, so $h^{(k)}(z) = F^{(k)}(z) = \int_0^\infty (-v)^k e^{-zv}\, d\mu(v)$ by Section 2. So
$$h(\sigma) = \sum_{k \geq 0} \frac{(\sigma - z)^k}{k!} F^{(k)}(z) = \sum_{k \geq 0} \int_0^\infty \frac{((z - \sigma)v)^k}{k!} e^{-zv}\, d\mu(v),$$
and the series converges. Every term is a nonnegative real number, since $z - \sigma > 0$, $v \geq 0$ and $\mu \geq 0$. By the theorem of Tonelli we can change the sum and the integral:
$$\sum_{k \geq 0} \int_0^\infty \frac{((z - \sigma)v)^k}{k!} e^{-zv}\, d\mu(v) = \int_0^\infty e^{(z - \sigma)v} e^{-zv}\, d\mu(v) = F(\sigma).$$
So $F(\sigma) = h(\sigma) < \infty$ for every $\sigma \in (a + \delta - \varepsilon, a + \delta)$. Since $\delta > 0$ is arbitrary and $F(\sigma) < \infty$ for $\sigma > a$ already, $F(\sigma) < \infty$ for every $\sigma > a - \varepsilon$. $\square$

The positivity of $\mu$ is used once, in Step 3, for the change of the sum and the integral with no condition of convergence. The analyticity of $F$ to the right of $a$ is used in Step 1, to glue $g$ and $F$. The rest is complex analysis.

### The classical forms

**Theorem (Landau).** Let $\mu$ be a positive Borel measure on $[0, \infty)$ whose abscissa of convergence $\sigma_c$ is finite. Then $F$ is not analytic at $\sigma_c$: there is no function analytic on a disc about $\sigma_c$ that is equal to $F$ on the part of the disc with $\operatorname{Re} s > \sigma_c$. Also, if $F$ continues analytically to the disc $|s - a| < \varepsilon$ about a real point $a \geq \sigma_c$, in this sense, then $\sigma_c \leq a - \varepsilon$.

*Proof.* The second statement is the local theorem, applied at $a$: it gives $F(\sigma) < \infty$ for $\sigma > a - \varepsilon$, so $\sigma_c \leq a - \varepsilon$. With $a = \sigma_c$ it gives $\sigma_c \leq \sigma_c - \varepsilon$, which is false. $\square$

So the distance from a real point $a > \sigma_c$ to the nearest singularity of $F$ is exactly $a - \sigma_c$, and the nearest singularity is the real point $\sigma_c$. This is the strongest sense in which the real axis decides.

**Corollary (Landau's theorem for Dirichlet series).** Let $a_n \geq 0$ for every $n$, and let the series $\alpha(s) = \sum_n a_n n^{-s}$ have a finite abscissa of convergence $\sigma_c$. Then $\alpha$ is not analytic at $s = \sigma_c$.

*Proof.* Apply the theorem to $\mu = \sum_n a_n \delta_{\log n}$. Its transform is $\alpha$, and its abscissa of convergence is $\sigma_c$. $\square$

This is Montgomery and Vaughan, *Multiplicative Number Theory I*, Theorem 1.7. The same proof works if $a_n \geq 0$ only for $n \geq n_0$, since a finite Dirichlet series is entire.

**Corollary (Landau's theorem for Mellin integrals).** Let $A : [1, \infty) \to \mathbb{R}$ be bounded and measurable on each interval $[1, X]$, and let $X_0 \geq 1$ be such that $A(x) \geq 0$ for $x > X_0$. Let $\sigma_c$ be the infimum of the real $\sigma$ with $\int_{X_0}^\infty A(x) x^{-\sigma}\, dx < \infty$, and suppose that $\sigma_c$ is finite. Then $F(s) = \int_1^\infty A(x) x^{-s}\, dx$ is analytic on $\operatorname{Re} s > \sigma_c$, and it is not analytic at $s = \sigma_c$.

*Proof.* Write $F = F_1 + F_2$, with $F_1(s) = \int_1^{X_0} A(x) x^{-s}\, dx$ and $F_2(s) = \int_{X_0}^\infty A(x) x^{-s}\, dx$. The function $F_1$ is entire, since its integrand is bounded and analytic in $s$ on a bounded interval. The substitution $x = e^v$ gives $F_2(s) = \int_0^\infty e^{-sv}\, d\mu(v)$ with $d\mu(v) = A(e^v) e^v\, dv$ on $v > \log X_0$, a positive measure with abscissa $\sigma_c$. Section 2 gives the analyticity of $F_2$ on $\operatorname{Re} s > \sigma_c$, and the theorem says that $F_2$, and so $F = F_1 + F_2$, is not analytic at $\sigma_c$. $\square$

This is Lemma 15.1 of Montgomery and Vaughan, which the source cites. Montgomery and Vaughan ask $A$ to be Riemann integrable on each finite interval. Measurable and bounded is enough for the proof above.

**Example (Pringsheim's theorem).** Let $f(w) = \sum_{n \geq 0} a_n w^n$ be a power series with $a_n \geq 0$ and with radius of convergence $\rho \in (0, \infty)$. Then $f$ has a singularity at the real point $w = \rho$. Indeed, let $\mu = \sum_n a_n \delta_n$. Its transform is $F(s) = \sum_n a_n e^{-ns} = f(e^{-s})$, with abscissa $\sigma_c = -\log \rho$, by the formula for the radius of convergence. If $f$ continued analytically to a disc about $\rho$, then $s \mapsto f(e^{-s})$ would continue analytically to a disc about $\sigma_c$, since $e^{-\sigma_c} = \rho$. This contradicts the theorem. For example, $\sum_n w^n = 1/(1 - w)$ has its pole at $1$, while $\sum_n (-1)^n w^n = 1/(1 + w)$, with coefficients of both signs, is analytic at $w = 1$.

### Continuation along the real axis

The applications do not know the abscissa in advance. They know a continuation of the transform with poles, and they know that no pole is real. The next corollary turns this into convergence.

**Corollary (Continuation along the real axis).** Let $\mu$ be a positive Borel measure on $[0, \infty)$ with $F(\sigma_1) < \infty$ for some real $\sigma_1$. Let $\beta < \sigma_1$, and let $G$ be meromorphic on the half-plane $\operatorname{Re} s > \beta$, with $G(s) = F(s)$ for $\operatorname{Re} s > \sigma_1$. Suppose that $G$ has no pole on the real half-line $(\beta, \infty)$. Then $\sigma_c \leq \beta$, and every pole of $G$ in $\operatorname{Re} s > \beta$ is removable: $G = F$ off the poles, and $F$ is analytic on $\operatorname{Re} s > \beta$.

*Proof.* Let $P$ be the set of poles of $G$. It is closed and discrete in the half-plane $\operatorname{Re} s > \beta$. Suppose that $\sigma_c > \beta$. The set $\Omega = \{s : \operatorname{Re} s > \sigma_c\} \setminus P$ is open and connected, since the complement of a closed discrete set in a connected open subset of $\mathbb{C}$ is connected. The functions $G$ and $F$ are analytic on $\Omega$ and equal on $\operatorname{Re} s > \sigma_1$, so they are equal on $\Omega$ by the identity theorem. The point $\sigma_c$ is real and $> \beta$, so it is not a pole, and $G$ is analytic on a disc $D$ about $\sigma_c$ that does not meet $P$. On $D \cap \{\operatorname{Re} s > \sigma_c\}$, a subset of $\Omega$, we have $G = F$. So $F$ is analytic at $\sigma_c$ in the sense of the theorem, which is false. So $\sigma_c \leq \beta$. Then $F$ is analytic on $\operatorname{Re} s > \beta$, and the same use of the identity theorem gives $G = F$ off $P$. A meromorphic function that is equal to an analytic function off a discrete set has only removable singularities. $\square$

The hypothesis on the real axis cannot be dropped: for $d\mu = e^{\beta' v}\, dv$ with $\beta < \beta'$, the transform $1/(s - \beta')$ is meromorphic on $\mathbb{C}$, and its only pole is real. Volume 1 proves a form in which real poles are allowed, if their residues have the right sign ([The model case](/chapter/landau-criterion/#the-model-case), Corollary (The residue at the abscissa)): at the abscissa, a simple pole of the continuation has a positive residue. That form is the one in the source, and Section 5 compares the two.
