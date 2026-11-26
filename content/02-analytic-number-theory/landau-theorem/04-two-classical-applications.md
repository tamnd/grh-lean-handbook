---
title: Two classical applications
lean:
  - Lib/Analytic/Landau.lean
  - Lib/Analytic/EntireLFunction.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Two classical applications

This section gives two classical uses of Landau's theorem. The first is Landau's proof that $L(1, \chi) \neq 0$ for a real nonprincipal character $\chi$. It applies the theorem to a Dirichlet series with nonnegative coefficients. The second is the principle that a one-sided bound for an error term excludes the poles of its transform, if no pole is real. It applies the theorem to a Mellin integral, and it is the model of the use in the source. The section ends with the change that the source makes to this principle.

### The value at 1 of a real character

Let $\chi$ be a real nonprincipal Dirichlet character modulo $q$, so that $\chi(n) \in \{-1, 0, 1\}$. We use two classical facts. First, the series $L(s, \chi) = \sum_n \chi(n) n^{-s}$ converges for $\operatorname{Re} s > 0$, by partial summation, since the sums $\sum_{n \leq x} \chi(n)$ are bounded by $q$. So $L(s, \chi)$ is analytic on $\operatorname{Re} s > 0$. Second, $\zeta(s) - 1/(s - 1)$ continues to an analytic function on $\operatorname{Re} s > 0$, by the formula $\zeta(s) = s/(s - 1) - s\int_1^\infty \{x\} x^{-s-1}\, dx$, where $\{x\}$ is the fractional part. [Dirichlet L-functions and zero symmetry](/chapter/dirichlet-l-functions/) gives the continuation of both functions to $\mathbb{C}$.

**Proposition (Landau).** Let $\chi$ be a real nonprincipal Dirichlet character. Then $L(1, \chi) \neq 0$.

*Proof.* Step 1: the coefficients. For $\operatorname{Re} s > 1$ both series converge absolutely, and
$$\zeta(s) L(s, \chi) = \sum_{n \geq 1} a_n n^{-s}, \qquad a_n = \sum_{d \mid n} \chi(d).$$
The function $a$ is multiplicative, as the convolution of two multiplicative functions. At a prime power, $a_{p^k} = \sum_{j = 0}^k \chi(p)^j$. This is $k + 1$ if $\chi(p) = 1$, it is $1$ if $\chi(p) = 0$, and if $\chi(p) = -1$ it is $1$ for $k$ even and $0$ for $k$ odd. So $a_n \geq 0$ for every $n$, and $a_{m^2} \geq 1$ for every $m \geq 1$.

Step 2: the continuation. Suppose that $L(1, \chi) = 0$. The function $G(s) = \zeta(s) L(s, \chi)$ is analytic on $\operatorname{Re} s > 0$ away from $s = 1$. At $s = 1$ the simple pole of $\zeta$ meets the zero of $L(s, \chi)$, so $G$ has a removable singularity there. So $G$ is analytic on $\operatorname{Re} s > 0$, and in particular it has no pole on $(0, \infty)$.

Step 3: Landau. Apply [Corollary](/chapter/landau-theorem/#landaus-theorem) (Continuation along the real axis) of Section 3 to $\mu = \sum_n a_n \delta_{\log n}$, with $\sigma_1 = 2$ and $\beta = 0$. It gives $\sigma_c \leq 0$. So the series $\sum_n a_n n^{-1/2}$ converges. But by Step 1,
$$\sum_n a_n n^{-1/2} \geq \sum_{m \geq 1} a_{m^2}\, m^{-1} \geq \sum_{m \geq 1} \frac{1}{m} = \infty.$$
This is a contradiction. $\square$

The proof does not use the class number formula and does not use a bound for $L(1, \chi)$. It uses the sign of the coefficients and the half-plane of analyticity of $L(s, \chi)$. A complex character is easier: then $\prod_{\chi \bmod q} L(s, \chi)$ has nonnegative coefficients, and a zero of $L(s, \chi)$ at $1$ would come with a zero of $L(s, \bar\chi)$ at $1$, which is too much for the pole of $L(s, \chi_0)$ (Davenport, *Multiplicative Number Theory*, Chapter 4).

**Remark (Formalization).** The source does not prove this proposition. It takes the non-vanishing of $L(s, \chi)$ on $\operatorname{Re} s \geq 1$ from Mathlib, as `DirichletCharacter.LFunction_ne_zero_of_one_le_re` (Mathlib), and uses it in [Landau's criterion](/chapter/landau-criterion/) for the real points $x \geq 1$. The module docstring of the Mathlib file says that its proof for a quadratic character is a positivity argument of the same kind: $L(s, \chi)\zeta(s)$ has nonnegative coefficients and is positive for large real $s$, but vanishes at $s = -2$. So this application of the classical theorem is in the background of the source, through Mathlib, and not through `Lib/Analytic/Landau.lean`.

### One-sided bounds and poles

The second application is a principle that goes back to Landau and that Montgomery and Vaughan, *Multiplicative Number Theory I*, Chapter 15, use for the oscillation of error terms in prime number theory.

**Theorem (A one-sided bound excludes the poles).** Let $A : [1, \infty) \to \mathbb{R}$ be measurable and bounded on each interval $[1, X]$, and suppose that $\int_1^\infty |A(x)|\, x^{-\sigma_1}\, dx < \infty$ for some real $\sigma_1$. Let $\beta < \sigma_1$, and suppose that $F(s) = \int_1^\infty A(x) x^{-s}\, dx$, defined for $\operatorname{Re} s > \sigma_1$, continues to a meromorphic function $G$ on $\operatorname{Re} s > \beta$ with no pole on the real half-line $(\beta, \infty)$. If $A(x) \geq 0$ for all large $x$, or $A(x) \leq 0$ for all large $x$, then $G$ has no pole in $\operatorname{Re} s > \beta$.

*Proof.* Replacing $A$ by $-A$, we can suppose that $A(x) \geq 0$ for $x > X_0$. Write $F = F_1 + F_2$ as in the proof of [Corollary](/chapter/landau-theorem/#landaus-theorem) (Landau's theorem for Mellin integrals), with $F_1$ the integral over $[1, X_0]$, an entire function. Then $F_2$ is the transform of the positive measure $d\mu(v) = A(e^v)e^v\, dv$ on $v > \log X_0$, it converges at $\sigma_1$ by the hypothesis, and $G - F_1$ is a meromorphic continuation of $F_2$ to $\operatorname{Re} s > \beta$ with no real pole. By the corollary on continuation along the real axis, every pole of $G - F_1$ is removable. Since $F_1$ is entire, the same holds for $G$. $\square$

**Corollary (Oscillation).** Let $A$, $\sigma_1$, $\beta$ and $G$ be as in the theorem, and suppose that $G$ has a pole at a point $\rho$ with $\operatorname{Re} \rho > \beta$. Let $\beta'$ be real with $\beta \leq \beta' < \operatorname{Re} \rho$. Then $A(x) > x^{\beta' - 1}$ for arbitrarily large $x$, and $A(x) < -x^{\beta' - 1}$ for arbitrarily large $x$.

*Proof.* Let $A_\pm(x) = x^{\beta' - 1} \mp A(x)$, and let $\sigma_1' > \max(\sigma_1, \beta')$. Then $\int_1^\infty |A_\pm(x)|\, x^{-\sigma_1'}\, dx < \infty$, and for $\operatorname{Re} s > \sigma_1'$ the transform of $A_\pm$ is $1/(s - \beta') \mp F(s)$. It continues to the meromorphic function $1/(s - \beta') \mp G(s)$ on $\operatorname{Re} s > \beta'$. This function has no pole on $(\beta', \infty)$, and it has a pole at $\rho$, since $\rho \neq \beta'$. If $A(x) \leq x^{\beta' - 1}$ for all large $x$, then $A_+ \geq 0$ for all large $x$, and the theorem, with $\beta'$ in place of $\beta$, says that there is no pole in $\operatorname{Re} s > \beta'$. This is false. So $A(x) > x^{\beta' - 1}$ for arbitrarily large $x$. The function $A_-$ gives the other inequality. $\square$

**Example (The oscillation of $\psi(x) - x$).** Let $\psi(x) = \sum_{n \leq x} \Lambda(n)$ and $A(x) = (\psi(x) - x)/x$. Since $\psi(x) \leq x \log x$, we can take $\sigma_1 = 2$. For $\operatorname{Re} s > 1$, partial summation gives $\int_1^\infty \psi(x) x^{-s-1}\, dx = -\zeta'(s)/(s\zeta(s))$, so
$$F(s) = \int_1^\infty (\psi(x) - x)\, x^{-s-1}\, dx = -\frac{\zeta'(s)}{s\,\zeta(s)} - \frac{1}{s - 1}.$$
The right side $G$ is meromorphic on $\mathbb{C}$. At $s = 1$, write $-\zeta'/\zeta(s) = 1/(s - 1) + c + O(s - 1)$. Then $-\zeta'/(s\zeta) = 1/(s(s - 1)) + c/s + O(s - 1)$, and $1/(s(s - 1)) = 1/(s - 1) - 1/s$, so $G$ is analytic at $1$. In $\operatorname{Re} s > 0$ the other poles of $G$ are the zeros $\rho$ of $\zeta$, with residue $-\operatorname{ord}_\rho \zeta/\rho \neq 0$. None of them is real: for $0 < \sigma < 1$ the alternating series $\eta(\sigma) = (1 - 2^{1 - \sigma})\zeta(\sigma)$ is positive and $1 - 2^{1 - \sigma} < 0$, so $\zeta(\sigma) < 0$. So the theorem applies with $\beta = 0$. Let $\Theta$ be the supremum of the real parts of the zeros of $\zeta$ in $0 < \operatorname{Re} s < 1$. The zeros exist (Davenport, *Multiplicative Number Theory*, Chapter 15) and are symmetric under $\rho \mapsto 1 - \bar\rho$, so $\Theta \geq 1/2$. The corollary gives, for every $\beta'$ with $0 < \beta' < \Theta$,
$$\psi(x) - x > x^{\beta'} \quad \text{and} \quad \psi(x) - x < -x^{\beta'} \qquad \text{for arbitrarily large } x.$$
In particular $\psi(x) - x = \Omega_\pm(x^{1/2 - \varepsilon})$ for every $\varepsilon > 0$. Sharper results of this kind, due to Littlewood and others, are in Montgomery and Vaughan, Chapter 15.

### The sign that the source needs

The theorem asks that no pole lies on the real half-line. For $\zeta$ this is a theorem, by the sign of $\eta$. For an L-function $L(s, \chi)$ of a real character it is the open question of real zeros, and of Siegel zeros near $1$. The source cannot assume it. It changes the principle in two ways.

First, it allows real poles, if the residues have the right sign. The form is [Corollary](/chapter/landau-criterion/#the-model-case) (The residue at the abscissa) of Volume 1: at the abscissa, a simple pole of the continuation has a positive residue. So an upper bound for $A$ excludes the poles if every real pole has a residue of real part $\leq 0$ for the transform of $x^{\beta - 1} - A(x)$, that is, of real part $\geq 0$ for the transform of $A$. This is the hypothesis $\operatorname{Re} r(x) \geq 0$ of [Theorem](/decl/New.IsPolar.landau/).

Second, it chooses the error term so that the real zeros give residues of this sign. The weight $1/n - 1/x$ in place of the plain count turns the residue $-\operatorname{ord}_\rho\zeta/\rho$ of the example above into $\operatorname{ord}_\rho \zeta/(\rho(1 - \rho))$, which is $\geq 0$ at a real $\rho \in (0, 1)$. Volume 1 explains this change ([The model case](/chapter/landau-criterion/#the-model-case), the part on the weight $1/n - 1/x$), and [the weighted prime remainder](/chapter/weighted-prime-remainder/) computes the residues for $R_{q_0}$. The zeros of the twists $L(s, \psi\chi_K)$ still give residues of the wrong sign, and [Landau's criterion](/chapter/landau-criterion/) removes them by the choice of the prime $d$.
