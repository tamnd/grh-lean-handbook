---
title: A one-sided bound and the zeros
lean:
  - New/Reduction/Zeros/Criterion.lean
  - Lib/Analytic/Landau.lean
  - Lib/Analytic/QuadraticTwist.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## A one-sided bound and the zeros

This chapter proves the step of the proof that turns a bound for a sum over primes into the absence of zeros of L-functions. The bound has one side only: it bounds a remainder from above, and it says nothing about how negative the remainder can be. The conclusion is that no Dirichlet L-function modulo $q_0$ vanishes in a half-plane $\operatorname{Re} s > \beta$. The tool is a theorem of Landau from 1905 on integrals of one sign. The step is the criterion `New.LFunction_ne_zero_of_primeRemainder_le` of the source, and it is the last analytic step before the proof of the theorem.

### Where the chapter sits

[The plan](/chapter/theorem-and-plan/) of the proof has three layers. At the bottom, Theorems A, B and C of Volumes 9 to 11 give a lattice inequality. In the middle, [the main inequality and the end of the proof](/chapter/main-inequality/) turns the lattice inequality into a one-sided bound for a weighted prime remainder $R_{q_0}$:
$$R_{q_0}(y) \leq y^{-1/2 + \varepsilon} \qquad \text{for all large } y.$$
At the top, this chapter turns the bound into the non-vanishing of $L(s, \psi)$ for every character $\psi$ modulo $q_0$ and every $s \neq 1$ with $\operatorname{Re} s > 1/2$. The last chapter of the volume then passes from the modulus $q_0$ to an arbitrary modulus $q$. [From the half-plane to the line](/chapter/half-plane-to-line/) then gives the zeros on the critical line.

The remainder $R_{q_0}$ is defined in [the weighted prime remainder](/chapter/weighted-prime-remainder/). It depends on a prime $d \equiv 7 \bmod 8$ and on the imaginary quadratic field $K = \mathbb{Q}(\sqrt{-d})$. With $\chi_K = (\cdot / d)$ and $\Lambda$ the von Mangoldt function, the weight is
$$\lambda(n) = \Lambda(n)\bigl(1 - \chi_K(n)\bigr) \quad \text{for } n \equiv 1 \bmod q_0, \qquad \lambda(n) = 0 \quad \text{otherwise},$$
and
$$R_{q_0}(x) = \sum_{n \leq x} \lambda(n)\Bigl(\frac{1}{n} - \frac{1}{x}\Bigr) - \frac{\log x}{\varphi(q_0)} - c_{q_0},$$
with a constant $c_{q_0}$ that makes $R_{q_0}(x) \to 0$. The factor $1 - \chi_K(p)$ is $2$ for a prime $p$ that is inert in $K$, $1$ for the ramified prime $d$, and $0$ for a prime that splits.

### The three ideas

The first idea is Landau's theorem. A Laplace transform $\int_0^\infty e^{-sv}\, d\mu(v)$ of a positive measure has a singularity at the real point where it stops converging. A one-sided bound $R(y) \leq y^{\beta - 1}$ makes $K y^\beta - y R(y)$ positive for a suitable $K$, and so gives a positive measure whose transform is $K/(s - \beta)$ minus the transform of $R$. If the residues of the transform of $R$ at the real points have the right sign, the transform of the measure converges in all of $\operatorname{Re} s > \beta$, and the transform of $R$ has no pole there. Section 2 does the classical case, the Riemann zeta function. Section 3 proves the form of the theorem that the source uses.

The second idea is the sign of the residues. The transform of $R_{q_0}$ has a pole at each zero of $L(s, \psi)$ and at each zero of the twist $L(s, \psi\chi_K)$, for the characters $\psi$ modulo $q_0$. The residue at a zero $\rho$ is
$$\frac{n(\rho) - n'(\rho)}{\varphi(q_0)\, \rho\, (1 - \rho)},$$
where $n(\rho)$ is the sum of the orders of the zeros of the $L(s, \psi)$ at $\rho$, and $n'(\rho)$ is the same sum for the twists. The zeros of the twists enter with a minus sign, because the weight is $1 - \chi_K$. Since $x(1 - x) > 0$ on $(0, 1)$, the zeros of the twists give real residues of the wrong sign. Section 4 explains this sign.

The third idea is the choice of $d$. Landau's theorem needs the right sign at every real point to the right of $\beta$. The conclusion is that the residue at $\rho$ is zero, and this gives $n(\rho) = 0$ only if $n'(\rho) = 0$. So the criterion needs one prime $d$ whose twists have no zeros at $\rho$ and on the real half-line $[\beta, \infty)$. A zero density theorem for quadratic twists gives such a $d$ in each class of primes modulo $q_0$, for each bounded box $\operatorname{Re} s \geq \beta$, $|\operatorname{Im} s| \leq H$. The prime $d$ depends on the height $H = |\operatorname{Im} \rho|$. So the hypothesis of the criterion is a bound for every prime $d$ of the class. Section 5 states the density theorem and proves the criterion.

### What the chapter uses

The chapter uses three results from other chapters, and states each in full with a link to its proof: the transform of $R_{q_0}$ and its residues from [the weighted prime remainder](/chapter/weighted-prime-remainder/) (Section 4), the zero density theorem for quadratic twists from [Pólya-Vinogradov and quadratic twists](/chapter/polya-vinogradov/) in Volume 2 (Section 5), and the one-sided bound from [the main inequality and the end of the proof](/chapter/main-inequality/) (Section 5). It also uses classical facts that Lean takes from Mathlib: the non-vanishing of $L(s, \psi)$ on $\operatorname{Re} s \geq 1$, the identity theorem, and the divergence of $\sum \log p / p$ over the primes of an invertible class. Section 3 proves Landau's theorem with all its steps, and [Landau's theorem](/chapter/landau-theorem/) in Volume 2 treats it again.

The source claims that the steps of this chapter are checked by Lean, and the checks that the source reports would confirm this. This book has not rerun the checks (Volume 0, Chapter 2).
