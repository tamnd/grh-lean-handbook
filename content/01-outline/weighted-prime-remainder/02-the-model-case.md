---
title: The model case
lean:
  - New/Reduction/Zeros/PrimeError.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The model case

This section treats the classical case $\lambda = \Lambda$, with no class and no twist. It shows where each term of $R_q$ comes from. Nothing in this section is in the source, and the rest of the book does not use it.

### The explicit formula for ψ(x)

Let $\psi(x) = \sum_{n \leq x} \Lambda(n)$, and let $\psi_0(x)$ be $\psi(x)$ at the points that are not prime powers, and $\psi(x) - \Lambda(x)/2$ at the prime powers. The classical explicit formula (Davenport, *Multiplicative Number Theory*, Chapter 17) is
$$\psi_0(x) = x - \sum_\rho \frac{x^\rho}{\rho} - \log 2\pi - \tfrac{1}{2}\log\bigl(1 - x^{-2}\bigr), \qquad x > 1,$$
where $\rho$ runs over the zeros of $\zeta$ in the strip $0 < \operatorname{Re} s < 1$, with multiplicity, and the sum is the limit as $T \to \infty$ of the sum over $|\operatorname{Im} \rho| < T$. The sum over $\rho$ converges only conditionally, since $\sum 1/|\rho|$ diverges.

The standard remedy is to smooth the sum. The source uses one integration:
$$S(x) = \int_1^x \frac{\psi(t)}{t^2}\, dt = \sum_{n \leq x} \Lambda(n) \int_n^x \frac{dt}{t^2} = \sum_{n \leq x} \Lambda(n)\Bigl(\frac{1}{n} - \frac{1}{x}\Bigr), \qquad x \geq 1.$$
The weight $1/n - 1/x$ is continuous in $x$ and vanishes at $x = n$, so $S$ is continuous. Mertens's theorem gives $\sum_{n \leq x} \Lambda(n)/n = \log x + O(1)$ and Chebyshev's bound gives $\psi(x) = O(x)$, so $S(x) = \log x + O(1)$. The question is the constant, and the error.

### The Mellin transform of a weighted sum

**Lemma (The transform of the weight).** Let $a : \mathbb{N} \to \mathbb{C}$, and let $\sigma > 1$ with $\sum_{n \geq 1} |a(n)| n^{-\sigma} < \infty$. Put $A(s) = \sum a(n) n^{-s}$ and $S_a(y) = \sum_{1 \leq n \leq y} a(n)(1/n - 1/y)$. Then for $\operatorname{Re} s = \sigma$,
$$\int_1^\infty S_a(y)\, y^{-s}\, dy = \frac{A(s)}{s(s - 1)}.$$
Also $\int_1^\infty \bigl(\sum_{n \leq y} a(n)/n\bigr) y^{-s}\, dy = A(s)/(s - 1)$ and $\int_1^\infty \bigl(y^{-1}\sum_{n \leq y} a(n)\bigr) y^{-s}\, dy = A(s)/s$.

Not in the source. The source proves only the two simple identities, for its weight $\lambda_q$, in the variable $v = \log y$ and for $\operatorname{Re} s > 2$: `New.LSeries_lambdaKResidueClass` (New/Reduction/Zeros/PrimeError.lean).

*Proof.* For $n \geq 1$ and $\operatorname{Re} s > 1$,
$$\int_n^\infty \frac{y^{-s}}{n}\, dy = \frac{n^{-s}}{s - 1}, \qquad \int_n^\infty y^{-1-s}\, dy = \frac{n^{-s}}{s}, \qquad \int_n^\infty \Bigl(\frac{1}{n} - \frac{1}{y}\Bigr) y^{-s}\, dy = \frac{n^{-s}}{s - 1} - \frac{n^{-s}}{s} = \frac{n^{-s}}{s(s - 1)}.$$
Write $S_a(y) = \sum_n a(n)(1/n - 1/y)\mathbf{1}_{y \geq n}$ and exchange the sum and the integral. The exchange is allowed by Tonelli's theorem, since $1/n - 1/y \geq 0$ for $y \geq n$ and the computation with $|a(n)|$ and $\sigma$ in place of $a(n)$ and $s$ gives $\sum |a(n)| n^{-\sigma}/(\sigma(\sigma - 1)) < \infty$. The other two identities are the first two integrals, summed in the same way. $\square$

The two simple identities are the case $r = 0$ and the case $r = 1$ of the partial summation of the source ([Lemma](/decl/New.LSeries_lambdaKResidueClass/)). The weight $1/n - 1/y$ is their difference. It turns the kernel $1/(s - 1)$ into $1/(s(s - 1))$, which decays like $|s|^{-2}$. So the explicit formula for $S$ converges absolutely.

### The transform of the model remainder

Apply the lemma with $a = \Lambda$, so that $A(s) = -\zeta'/\zeta(s)$ for $\operatorname{Re} s > 1$. Put $Z(s) = (s - 1)\zeta(s)$. It is entire, $Z(1) = 1$, and the Laurent expansion $\zeta(s) = 1/(s - 1) + \gamma + O(s - 1)$ gives $Z'(1)/Z(1) = \gamma$. From $\zeta'/\zeta = Z'/Z - 1/(s - 1)$,
$$-\frac{\zeta'}{\zeta}(s) = \frac{1}{s - 1} - \frac{Z'}{Z}(s) = \frac{s}{s - 1} + G(s), \qquad G(s) = -\frac{Z'}{Z}(s) - 1.$$
The function $G$ is meromorphic on $\mathbb{C}$. It is analytic on $\operatorname{Re} s \geq 1$, since $\zeta$ has no zero there, and $G(1) = -1 - \gamma$. So for $\operatorname{Re} s > 1$,
$$\int_1^\infty S(y)\, y^{-s}\, dy = \frac{1}{(s - 1)^2} + \frac{G(s)}{s(s - 1)}.$$
The first term is the main term: $\int_1^\infty (\log y)\, y^{-s}\, dy = 1/(s - 1)^2$. The constant has $\int_1^\infty y^{-s}\, dy = 1/(s - 1)$. So for a real constant $c$, the remainder $R(x) = S(x) - \log x - c$ has the transform
$$\int_1^\infty R(y)\, y^{-s}\, dy = \frac{G(s)/s - c}{s - 1}, \qquad \operatorname{Re} s > 1.$$
The right side continues to a meromorphic function on $\mathbb{C}$. The term $\log x$ has removed the double pole at $s = 1$. The numerator is analytic at $s = 1$, with the value $G(1) - c$. So the continuation has no pole at $s = 1$ if and only if $c = G(1) = -1 - \gamma$. With this constant, $R$ is the function $R_1$ of this chapter for the weights $\Lambda$ in place of $\lambda$: the constant is the value at $1$ of a logarithmic derivative, less $1$.

The residues come from $G$. Let $\rho \neq 0, 1$ be a zero of $\zeta$ of order $m$. Then $Z$ has a zero of order $m$ at $\rho$, so $G = -Z'/Z - 1$ has a simple pole there with residue $-m$. The residue of the transform at $\rho$ is
$$\frac{-m}{\rho(\rho - 1)} = \frac{m}{\rho(1 - \rho)}.$$
At a point of $\operatorname{Re} s > 0$, $s \neq 1$, where $\zeta$ has no zero, the function $G$ is analytic, and the transform has no pole.

### The dictionary

The transform of the function $y \mapsto y^{\rho - 1}$ on $[1, \infty)$ is
$$\int_1^\infty y^{\rho - 1} y^{-s}\, dy = \frac{1}{s - \rho}, \qquad \operatorname{Re} s > \operatorname{Re} \rho.$$
So a term $r\, x^{\rho - 1}$ of $R(x)$ is a simple pole $r/(s - \rho)$ of the transform, and the residue is the coefficient. Read in this way, the computation above predicts the explicit formula for $S$.

**Proposition (The explicit formula for the weighted sum).** For $x \geq 1$,
$$S(x) = \log x - 1 - \gamma + \sum_\rho \frac{x^{\rho - 1}}{\rho(1 - \rho)} + \frac{\log 2\pi}{x} - \sum_{k \geq 1} \frac{x^{-2k-1}}{2k(2k + 1)},$$
where $\rho$ runs over the zeros of $\zeta$ in $0 < \operatorname{Re} s < 1$ with multiplicity. The sum over $\rho$ converges absolutely and uniformly in $x \geq 1$.

Not in the source. The source uses no explicit formula: it reads the zeros from the poles of the transform of $R_q$, by `New.isPolar_primeRemainder` (New/Reduction/Zeros/PrimeError.lean).

*Sketch.* Integrate the explicit formula for $\psi_0$ against $t^{-2}$ from $1$ to $x$, with the truncated form of the explicit formula in Davenport, Chapter 17, to justify the integration term by term. The main term gives $\log x$. A zero gives $-\int_1^x t^{\rho - 2} dt/\rho = (x^{\rho - 1} - 1)/(\rho(1 - \rho))$. The term $-\log 2\pi$ gives $-(1 - 1/x)\log 2\pi$. The last term is $\frac{1}{2}\sum_{k \geq 1} t^{-2k}/k$, and it gives $\sum_k (1 - x^{-2k-1})/(2k(2k + 1))$. The constants add up to
$$-\sum_\rho \frac{1}{\rho(1 - \rho)} - \log 2\pi + \sum_{k \geq 1}\frac{1}{2k(2k+1)} = -(2 + \gamma - \log 4\pi) - \log 2\pi + (1 - \log 2) = -1 - \gamma,$$
by $\sum_\rho 1/(\rho(1 - \rho)) = 2\sum_\rho \operatorname{Re}(1/\rho) = 2 + \gamma - \log 4\pi$ (Davenport, Chapter 12). The absolute convergence follows from $\sum_\rho |\rho|^{-2} < \infty$ and $|x^{\rho - 1}| \leq 1$. $\square$

The constant $-1 - \gamma$ of the proposition is the constant $G(1)$ that the transform predicts. Exercise 2 asks for the check of the numbers.

### What the model case shows

Put $R(x) = S(x) - \log x + 1 + \gamma$. The proposition gives
$$R(x) = \sum_\rho \frac{x^{\rho - 1}}{\rho(1 - \rho)} + O\bigl(x^{-1}\bigr).$$
Let $\Theta$ be the supremum of the real parts of the zeros. Then $R(x) = O(x^{\Theta - 1})$. Conversely, if $R(x) = O(x^{\beta - 1})$ for some $\beta < 1$, then $\int_1^\infty R(y) y^{-s} dy$ converges and is analytic in $\operatorname{Re} s > \beta$, so it has no pole there, and $\zeta$ has no zero there. So the Riemann hypothesis is equivalent to $R(x) = O(x^{-1/2 + \varepsilon})$ for every $\varepsilon > 0$.

The source needs less than a two-sided bound. Look at a real zero $\rho = \beta_0 \in (0, 1)$. Its term $m\, x^{\beta_0 - 1}/(\beta_0(1 - \beta_0))$ is positive. A real zero pushes $R$ up. Landau's theorem extends this to all zeros: since $\Lambda \geq 0$, an upper bound $R(x) \leq x^{\beta - 1}$ for all large $x$ already forces the transform to be analytic in $\operatorname{Re} s > \beta$. The input is the positivity of the residues at real points ([Landau's criterion](/chapter/landau-criterion/)). In the model case it is automatic.

In the weights of the source, the zeros of the twists $L(s, \psi\chi_K)$ enter with the sign $-$ (Section 5). This is the price of the weights $1 - \chi_K$.
