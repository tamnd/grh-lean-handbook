---
title: Logarithmic derivatives and their residues
lean:
  - Lib/Analytic/EntireLFunction.lean
decls:
  - New.LSeriesHasSum_mul_vonMangoldt
  - New.tendsto_sub_mul_of_continuousAt
  - New.analyticOrderAt_entireL_ne_top
  - New.analyticOrderNatAt_entireL_eq_zero_iff
  - New.tendsto_sub_mul_logDeriv_entireL_analyticOrderNatAt
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Logarithmic derivatives and their residues

Every explicit formula starts from the logarithmic derivative of an L-function. Its Dirichlet series has the von Mangoldt function as coefficients, and its poles are the zeros of the L-function. This section states the classical facts, then the forms that the source proves. The source needs much less than the classical theory: one identity of Dirichlet series in $\operatorname{Re} s > 1$, and one local fact at each point of $\mathbb{C}$.

### The classical theory

Let $\chi$ be a Dirichlet character modulo $N \geq 1$. For $\operatorname{Re} s > 1$ the Euler product $L(s, \chi) = \prod_p (1 - \chi(p)p^{-s})^{-1}$ converges absolutely, so $L(s, \chi) \neq 0$ there, and its logarithmic derivative is
$$-\frac{L'}{L}(s, \chi) = \sum_p \sum_{k \geq 1} \chi(p)^k (\log p)\, p^{-ks} = \sum_{n \geq 1} \chi(n)\Lambda(n)\, n^{-s}, \qquad \operatorname{Re} s > 1,$$
where $\Lambda$ is the von Mangoldt function (Davenport, *Multiplicative Number Theory*, Chapters 1 and 4). The function $L(s, \chi)$ continues to a meromorphic function on $\mathbb{C}$. It is entire if $\chi$ is not principal. If $\chi$ is principal it has one simple pole, at $s = 1$, with residue $\varphi(N)/N$.

The logarithmic derivative $f'/f$ of a meromorphic function $f$ that is not identically $0$ has a simple pole at each zero and at each pole of $f$. The residue is the order of the zero, or minus the order of the pole. So $L'/L(s, \chi)$ has a simple pole with residue $m$ at each zero of order $m$, and, for principal $\chi$, a simple pole with residue $-1$ at $s = 1$. This local fact is all that the source uses. The classical theory gives a global form of it.

**Theorem (Partial fractions).** Let $\chi$ be a primitive character modulo $N \geq 3$, and let $\mathfrak a = 0$ if $\chi(-1) = 1$ and $\mathfrak a = 1$ if $\chi(-1) = -1$. There is a constant $B(\chi)$ such that for every $s$ that is not a zero of $L(s, \chi)$ or a pole of $\Gamma((s + \mathfrak a)/2)$,
$$\frac{L'}{L}(s, \chi) = -\frac{1}{2}\log\frac{N}{\pi} - \frac{1}{2}\frac{\Gamma'}{\Gamma}\Bigl(\frac{s + \mathfrak a}{2}\Bigr) + B(\chi) + \sum_\rho \Bigl(\frac{1}{s - \rho} + \frac{1}{\rho}\Bigr),$$
where $\rho$ runs over the zeros of $L(s, \chi)$ in $0 < \operatorname{Re} s < 1$, with multiplicity. The sum converges absolutely and uniformly on compact sets that contain no zero.

This is Davenport, Chapter 12. Its proof needs the functional equation (Chapter 9), the theory of entire functions of order $1$ (Chapter 11), and the Hadamard product of the completed function $\xi(s, \chi)$. The trivial zeros, at $s = -\mathfrak a, -\mathfrak a - 2, \ldots$, are the poles of the term with $\Gamma'/\Gamma$. The formula for $\zeta$ is of the same kind, with an extra term $-1/(s - 1)$ (Davenport, Chapter 12). Iwaniec and Kowalski, *Analytic Number Theory*, Chapter 5, give the same theory for a general L-function with a functional equation.

The partial fraction formula is the input of the classical explicit formula of Section 3. The source does not prove it and does not use it.

### The series of χΛ in the form of the source

The source works with $\tilde L$ in place of $L$. For principal $\chi$, the factor $s - 1$ removes the pole, so $\tilde L(\cdot, \chi)$ is entire for every $\chi$, and it has no zero on $\operatorname{Re} s \geq 1$ ([Lemma](/decl/New.entireL_ne_zero/)). The pole of $L$ at $s = 1$ then appears as an explicit term.

**Lemma (The series of χΛ).** Let $\chi$ be a Dirichlet character modulo $N \geq 1$, and let $\operatorname{Re} s > 1$. Then the series $\sum_{n \geq 1} \chi(n)\Lambda(n) n^{-s}$ converges absolutely, and its sum is
$$\frac{\delta_\chi}{s - 1} - \frac{\tilde L'}{\tilde L}(s, \chi), \qquad \delta_\chi = \begin{cases} 1 & \text{if } \chi \text{ is principal,} \\ 0 & \text{otherwise.} \end{cases}$$

Lean: `New.LSeriesHasSum_mul_vonMangoldt` (Lib/Analytic/EntireLFunction.lean).

*Proof.* Mathlib proves the absolute convergence and the identity $\sum \chi(n)\Lambda(n)n^{-s} = -L'/L(s, \chi)$ for $\operatorname{Re} s > 1$, and $L(s, \chi) \neq 0$ there. If $\chi$ is not principal, $\tilde L = L$. If $\chi$ is principal, then $s \neq 1$, $\tilde L(s, \chi) = (s - 1)L(s, \chi)$, and the rule for the logarithmic derivative of a product gives $\tilde L'/\tilde L = 1/(s - 1) + L'/L$. $\square$

### The residues of the logarithmic derivative

The first lemma is a trivial case: no pole.

**Lemma (No pole at a point of continuity).** Let $f : \mathbb{C} \to \mathbb{C}$ be continuous at $s$. Then $(z - s)f(z) \to 0$ as $z \to s$, $z \neq s$.

Lean: `New.tendsto_sub_mul_of_continuousAt` (Lib/Analytic/EntireLFunction.lean).

*Proof.* The factor $z - s$ tends to $0$, and $f(z)$ tends to $f(s)$. $\square$

The order of a zero is finite only if the function is not identically $0$ near the point. For an entire function, the identity theorem reduces this to one value.

**Lemma (Finite order).** Let $\chi$ be a Dirichlet character modulo $N \geq 1$, and let $s \in \mathbb{C}$. Then $\tilde L(\cdot, \chi)$ has finite order at $s$. Its order at $s$ is $0$ if and only if $\tilde L(s, \chi) \neq 0$.

Lean: `New.analyticOrderAt_entireL_ne_top` (Lib/Analytic/EntireLFunction.lean), with `New.analyticOrderNatAt_entireL_eq_zero_iff` (Lib/Analytic/EntireLFunction.lean) for the second claim.

*Proof.* If the order at $s$ were infinite, $\tilde L(\cdot, \chi)$ would vanish on a neighbourhood of $s$, and so on $\mathbb{C}$ by the identity theorem, since it is entire. But $\tilde L(1, \chi) \neq 0$ ([Lemma](/decl/New.entireL_ne_zero/)). The order of an analytic function at a point is $0$ exactly when its value there is not $0$. $\square$

**Lemma (The residue of a logarithmic derivative).** Let $\chi$ be a Dirichlet character modulo $N \geq 1$, and let $s \in \mathbb{C}$. Then
$$(z - s)\,\frac{\tilde L'}{\tilde L}(z, \chi) \to \operatorname{ord}_s \tilde L(\cdot, \chi) \qquad (z \to s,\ z \neq s).$$

Lean: `New.tendsto_sub_mul_logDeriv_entireL_analyticOrderNatAt` (Lib/Analytic/EntireLFunction.lean).

*Proof.* Let $m = \operatorname{ord}_s \tilde L(\cdot, \chi)$, finite by the lemma above. Then $\tilde L(z, \chi) = (z - s)^m g(z)$ near $s$, with $g$ analytic at $s$ and $g(s) \neq 0$. For $z \neq s$ near $s$, $g(z) \neq 0$, and
$$\frac{\tilde L'}{\tilde L}(z, \chi) = \frac{m}{z - s} + \frac{g'}{g}(z).$$
So $(z - s)\tilde L'/\tilde L(z, \chi) = m + (z - s)g'(z)/g(z)$. The function $g'/g$ is analytic at $s$, and the lemma on points of continuity gives the limit $m$. $\square$

The lemma holds at every $s \in \mathbb{C}$. At a point where $\tilde L(s, \chi) \neq 0$ it says that there is no pole. At $s = 1$ for principal $\chi$ it says that $\tilde L'/\tilde L$ has no pole, since $\tilde L(1, \chi) \neq 0$: the pole of $L'/L$ at $1$ has moved into the term $\delta_\chi/(s - 1)$ of the series.

**Example (The principal character modulo 3).** Let $\chi_0$ be the principal character modulo $3$. Then $L(s, \chi_0) = (1 - 3^{-s})\zeta(s)$, and
$$\tilde L(s, \chi_0) = (1 - 3^{-s})(s - 1)\zeta(s).$$
The factor $1 - 3^{-s}$ vanishes at $s = 2\pi i k/\log 3$ for every $k \in \mathbb{Z}$, with order $1$. So $\tilde L(\cdot, \chi_0)$ has a zero of order $1$ at $s = 0$, since $\zeta(0) = -1/2 \neq 0$, and simple zeros on the line $\operatorname{Re} s = 0$. The partial fraction formula above is for primitive characters, and it does not see these zeros. The lemma of the source counts them, since $\operatorname{ord}_s$ is the order of the zero of $\tilde L$ itself. These zeros lie in $\operatorname{Re} s \leq 0$, so they play no role in the argument (Section 4). In $\operatorname{Re} s > 0$ the zeros of $\tilde L(\cdot, \chi)$ are those of $L(s, \chi^*)$ for the primitive character $\chi^*$ that induces $\chi$, with the same orders, since the Euler factors $1 - \chi^*(p)p^{-s}$ for $p \mid N$ do not vanish there.

**Remark (Formalization).** Three points. First, the source writes $\tilde L'/\tilde L$ with Mathlib's `logDeriv f z`, which is `deriv f z / f z`. At a zero of $f$ this is a division by $0$, of value $0$. The lemma above is a statement about limits with $z \neq s$, so this value plays no role in it. Second, the order is `analyticOrderNatAt`, the order as a natural number, which Mathlib sets to $0$ when the order is infinite. The lemma on finite order shows that this does not happen for $\tilde L$. Third, the source proves the residue lemma for every character, primitive or not, at every point, with no functional equation and no product formula. The classical theory gives more, a formula for $L'/L$ on all of $\mathbb{C}$ with a sum over the zeros. The argument needs only the residues, because Landau's lemma works with the poles one at a time.
