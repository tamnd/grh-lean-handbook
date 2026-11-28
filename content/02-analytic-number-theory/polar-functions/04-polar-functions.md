---
title: Polar functions
lean:
  - Lib/Analytic/EntireLFunction.lean
  - Lib/Analytic/Landau.lean
decls:
  - New.IsPolar
  - New.integrableOn_laplace_of_abs_le
  - New.laplace_pow
  - New.IsPolar.landau
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Polar functions

This section defines the polar functions of the source and proves their elementary properties. A polar function is a real function $E$ on $\mathbb{R}$, with a function $r$ on $\mathbb{C}$, such that the transform of $E$ continues to a meromorphic function whose poles in $\operatorname{Re} s > 0$ are at most simple, with residues $r$. The notion keeps from the explicit formula exactly what Landau's lemma needs: the location of the poles in the right half-plane and their residues. It drops the expansion of $E$ as a sum over the poles.

### The definition

The variable is $v = \log y$. For a function $R$ on $[1, \infty)$ put $E(v) = R(e^v)$. Then $\int_1^\infty R(y) y^{-s}\, dy = \int_0^\infty E(v) e^{(1 - s)v}\, dv$. The source uses the second form, and calls it the transform of $E$.

**Definition (Polar function).** Let $E : \mathbb{R} \to \mathbb{R}$ and $r : \mathbb{C} \to \mathbb{C}$. The function $E$ is *polar with residues $r$* if $E$ is measurable and there are a real number $C$ and a function $\Phi : \mathbb{C} \to \mathbb{C}$ with these four properties.

1. $\Phi$ is meromorphic on $\mathbb{C}$.
2. $|E(v)| \leq C e^v$ for every $v \geq 0$.
3. $\Phi(s) = \int_0^\infty E(v)\, e^{(1 - s)v}\, dv$ for every $s$ with $\operatorname{Re} s > 2$.
4. For every $\rho$ with $\operatorname{Re}\rho > 0$, $(z - \rho)\Phi(z) \to r(\rho)$ as $z \to \rho$, $z \neq \rho$.

Lean: `New.IsPolar` (Lib/Analytic/EntireLFunction.lean).

Volume 1 calls such a pair $(E, r)$ a polar pair ([Landau's criterion](/chapter/landau-criterion/)). Property 4 has three readings. If $\Phi$ is analytic at $\rho$, the limit is $0$, so $r(\rho) = 0$. If $\Phi$ has a simple pole at $\rho$, the limit is the residue. If $\Phi$ has a pole of order $2$ or more at $\rho$, the limit does not exist. So property 4 says that the poles of $\Phi$ in $\operatorname{Re} s > 0$ are at most simple, and that $r$ is the residue function there.

**Lemma (Convergence of the transform).** Let $E$ be measurable with $|E(v)| \leq C e^v$ for $v \geq 0$, and let $\operatorname{Re} s > 2$. Then $v \mapsto E(v)e^{(1 - s)v}$ is integrable on $(0, \infty)$.

Lean: `New.integrableOn_laplace_of_abs_le` (Lib/Analytic/EntireLFunction.lean).

*Proof.* The integrand is at most $C e^{(2 - \operatorname{Re} s)v}$ in absolute value, and $2 - \operatorname{Re} s < 0$. $\square$

**Lemma (The transform of a power).** Let $\operatorname{Re} s > 0$ and $k \in \mathbb{N}$. Then $\int_0^\infty t^k e^{-st}\, dt = k!/s^{k + 1}$.

Lean: `New.laplace_pow` (Lib/Analytic/EntireLFunction.lean).

*Proof.* For $\operatorname{Re} z < 0$, $\int_0^\infty e^{zt}\, dt = -1/z$. Differentiate $k$ times in $z$ under the integral sign, which is allowed on $\operatorname{Re} z < 0$, and put $z = -s$. $\square$

**Remark (Formalization).** A polar function is not a notion of the textbooks. The nearest classical object is a Laplace transform $\int_0^\infty e^{-sv}\, d\alpha(v)$ with a meromorphic continuation, as in Widder, *The Laplace Transform* (1941), Chapter II, and in the form of Landau's theorem in Montgomery and Vaughan, *Multiplicative Number Theory I*, Lemma 15.1, which the source cites. The definition of the source differs from that frame in these points. (a) $E$ is only measurable. No continuity and no bounded variation are asked. (b) The growth $|E(v)| \leq Ce^v$ is crude, and it fixes the half-plane $\operatorname{Re} s > 2$ of property 3. A smaller half-plane gives the same $\Phi$, by the identity theorem. (c) The integral is a Bochner integral, which Lean sets to $0$ when the integrand is not integrable. The lemma on convergence shows that this junk value does not occur in property 3. (d) $\Phi$ is meromorphic on all of $\mathbb{C}$, in the sense of Mathlib: near each point $x$, some power $(z - x)^n\Phi(z)$ is analytic. This sense does not look at the value $\Phi(x)$, so the values of $\Phi$ at its poles are arbitrary. (e) $r$ is the residue only in $\operatorname{Re}\rho > 0$. In $\operatorname{Re}\rho \leq 0$ the definition puts no condition on $r$, and $\Phi$ can have poles of any order there. The argument needs only the poles to the right of $\beta > 1/2$, so the restriction costs nothing.

### Elementary properties

**Lemma (The residues are unique).** Let $E$ be polar with residues $r$ and with residues $r'$. Then $r(\rho) = r'(\rho)$ for every $\rho$ with $\operatorname{Re}\rho > 0$.

Not in the source. The source uses one polar function only, the remainder of `New.isPolar_primeRemainder` (New/Reduction/Zeros/PrimeError.lean), with one residue function.

*Proof.* Let $\Phi$ and $\Phi'$ be the functions of the definition for $r$ and for $r'$. They are equal on $\operatorname{Re} s > 2$ by property 3. Let $P$ be the union of the sets of poles of $\Phi$ and $\Phi'$. It is discrete and closed, so $\mathbb{C} \setminus P$ is open and connected, and $\Phi = \Phi'$ on it by the identity theorem. So $(z - \rho)\Phi(z) = (z - \rho)\Phi'(z)$ on a punctured neighbourhood of every $\rho$, and the limits $r(\rho)$ and $r'(\rho)$ of property 4 are equal. $\square$

So the residue function of a polar function is a function of $E$ on $\operatorname{Re} s > 0$. This is why the source can state a residue formula that is a junk value at one point, as long as it is the true residue (Section 5).

**Lemma (Linearity).** Let $E$ be polar with residues $r$, let $E'$ be polar with residues $r'$, and let $a, b$ be real. Then $aE + bE'$ is polar with residues $ar + br'$.

Not in the source. The source proves the polar property of its one remainder directly, in `New.isPolar_primeRemainder` (New/Reduction/Zeros/PrimeError.lean), and never adds two polar functions.

*Proof.* Take $|a|C + |b|C'$ and $a\Phi + b\Phi'$. A linear combination of meromorphic functions is meromorphic. For $\operatorname{Re} s > 2$ both integrands are integrable by the lemma on convergence, so the integral of the combination is the combination of the integrals. Limits add. $\square$

The pieces of a polar function need not be polar. This is the point of the main terms of a prime remainder.

**Example (Exponentials).** Let $\beta$ be real with $\beta \leq 2$, and let $E(v) = e^{(\beta - 1)v}$. Then $|E(v)| \leq e^v$ for $v \geq 0$, and for $\operatorname{Re} s > 2$ the transform is $\int_0^\infty e^{(\beta - s)v}\, dv = 1/(s - \beta)$. Take $\Phi(s) = 1/(s - \beta)$. So $E$ is polar with the residues $r(\beta) = 1$ and $r(\rho) = 0$ for $\rho \neq \beta$, if $\beta > 0$. For $\beta = 1$ this says that the constant function $1$ is polar, with one pole, at $s = 1$, of residue $1$. For $\beta > 2$ the growth condition fails, and $E$ is not polar.

**Example (A double pole).** Let $E(v) = v$. By the lemma on the transform of a power, for $\operatorname{Re} s > 2$ the transform is $1/(s - 1)^2$. Let $\Phi$ be meromorphic on $\mathbb{C}$ and equal to the transform on $\operatorname{Re} s > 2$. By the identity theorem, $\Phi(s) = 1/(s - 1)^2$ off a discrete set, so $(z - 1)\Phi(z) = 1/(z - 1)$ for $z$ near $1$ off that set, and it has no limit. So $E$ is not polar for any $r$. In the variable $y = e^v$, $E$ is $\log y$, the main term of the weighted sum $\sum_{n \leq y}\Lambda(n)(1/n - 1/y)$ of Section 3. A prime remainder can be polar only after its main term $\log y/\varphi(q)$ is removed.

**Example (An oscillation).** Let $\rho_0 = \beta_0 + i\gamma_0$ with $0 < \beta_0 \leq 2$ and $\gamma_0 \neq 0$, let $c \in \mathbb{C}$, and let
$$E(v) = c\, e^{(\rho_0 - 1)v} + \bar c\, e^{(\bar\rho_0 - 1)v} = 2|c|\, e^{(\beta_0 - 1)v}\cos(\gamma_0 v + \arg c).$$
Then $E$ is real, $|E(v)| \leq 2|c|e^v$, and its transform is $c/(s - \rho_0) + \bar c/(s - \bar\rho_0)$. So $E$ is polar with $r(\rho_0) = c$, $r(\bar\rho_0) = \bar c$, and $r = 0$ at the other points of $\operatorname{Re} s > 0$. This is the contribution of a pair of complex zeros to a prime remainder.

**Lemma (A two-sided bound kills the poles).** Let $E$ be polar with residues $r$, and let $\beta > 0$. Suppose that there are $Y \geq 0$ and $C_1$ with $|E(v)| \leq C_1 e^{(\beta - 1)v}$ for $v \geq Y$. Then $r(\rho) = 0$ for every $\rho$ with $\operatorname{Re}\rho > \beta$.

Not in the source. The source proves a form with an upper bound only, which needs in exchange a hypothesis on the sign of the residues at real points: [Theorem](/decl/New.IsPolar.landau/).

*Proof.* Let $C$ and $\Phi$ be as in the definition. For $\operatorname{Re} s > \beta$ split the integral $A(s) = \int_0^\infty E(v)e^{(1 - s)v}\, dv$ at $Y$. On $(0, Y)$ the integrand is bounded by $|C|e^{(2 + |s|)Y}$, so this part is an entire function of $s$. On $(Y, \infty)$ the integrand is at most $C_1 e^{(\beta - \operatorname{Re} s)v}$, so this part converges absolutely and locally uniformly on $\operatorname{Re} s > \beta$, and it is analytic there. So $A$ is analytic on $\operatorname{Re} s > \beta$, and $A = \Phi$ on $\operatorname{Re} s > \max(\beta, 2)$. Let $P$ be the set of poles of $\Phi$. The set $\{\operatorname{Re} s > \beta\} \setminus P$ is open and connected, and $A = \Phi$ on it by the identity theorem. Let $\operatorname{Re}\rho > \beta$. Then $\operatorname{Re}\rho > 0$, and $(z - \rho)\Phi(z) = (z - \rho)A(z)$ on a punctured neighbourhood of $\rho$. The right side tends to $0$ by [Lemma](/decl/New.tendsto_sub_mul_of_continuousAt/). By property 4, $r(\rho) = 0$. $\square$

**Theorem (Landau's lemma for polar functions).** Let $E$ be polar with residues $r$, and let $\beta > 0$. Suppose that $\operatorname{Re} r(x) \geq 0$ for every real $x > \beta$, and that $E(v) \leq e^{(\beta - 1)v}$ for all large $v$. Then $r(\rho) = 0$ for every $\rho$ with $\operatorname{Re}\rho > \beta$.

Lean: `New.IsPolar.landau` (Lib/Analytic/Landau.lean).

The proof is in [Landau's criterion](/chapter/landau-criterion/), and [Landau's theorem](/chapter/landau-theorem/) treats it again. The examples show why each hypothesis is there. In the example of an oscillation with $c \neq 0$, there is no real pole, so the sign hypothesis holds for every $\beta$. The theorem then says that $E(v) \leq e^{(\beta - 1)v}$ for all large $v$ fails for every $\beta < \beta_0$, and this is true: the cosine is at least $1/2$ on a sequence of $v \to \infty$, so $E(v) \geq |c|e^{(\beta_0 - 1)v}$ there. Now take $E(v) = -e^{(\beta_0 - 1)v}$ with $0 < \beta_0 \leq 2$. It is polar with $r(\beta_0) = -1$. It is negative, so $E(v) \leq e^{(\beta - 1)v}$ holds for every $\beta > 0$. The conclusion fails at $\rho = \beta_0$ for every $\beta < \beta_0$. Here the sign hypothesis is the one that fails. In the prime remainder of the source such a term comes from a real zero of a twist $L(s, \psi\chi_K)$ (Section 5).

**Remark (Formalization).** The compact edition of the source has a stronger definition `IsPolar` (grh-compact). It adds one property: $(s - 1)\Phi(s)$ is analytic on $\operatorname{Re} s \geq 1$. With property 4 at $\rho = 1$, this rules out a pole at $s = 1$ that is not simple and fixes the behaviour on the line $\operatorname{Re} s = 1$. The compact edition uses the extra property in `IsPolar.exists_window_sub_mul_le` (grh-compact), a window lemma. Its docstring says that it replaces a pointwise prime number theorem in progressions when the second scale of the main inequality is chosen. The readable edition, which this book follows, has no such lemma. It uses polar functions only for Landau's lemma, and there the four properties above are enough.
