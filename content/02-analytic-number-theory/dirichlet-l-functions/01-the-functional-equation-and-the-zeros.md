---
title: The functional equation and the zeros
lean:
  - Lib/Analytic/ZeroSymmetry.lean
  - Lib/Analytic/DirichletTheta.lean
  - Lib/Analytic/EntireLFunction.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The functional equation and the zeros

This chapter gives the classical theory of Dirichlet L-functions that the rest of the book uses: characters, the L-function $L(s, \chi)$ and its continuation, the completed L-function $\Lambda(s, \chi)$, the functional equation, and the symmetry of the zeros. For each object it gives the textbook form first, with a source, then the form in which Mathlib or the source states it. Three files of the source belong here. The first proves the reflection of zeros for every character, primitive or not. The second proves the transformation formula of the theta series of a character and the formula for $L(s, \chi)$ as a Mellin transform. The third defines the entire L-function $\tilde L(s, \chi)$.

### Where the chapter sits

The argument of the source proves a statement about a half-plane: no Dirichlet L-function has a zero with $\operatorname{Re} s > 1/2$ ([the plan](/chapter/theorem-and-plan/)). The source states its main theorem for the critical line. The bridge between the two is the reflection $s \mapsto 1 - s$ of zeros. Volume 1, [From the half-plane to the line](/chapter/half-plane-to-line/), makes the deduction. It uses one theorem of this chapter, [Theorem](/decl/New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero/) of Section 5. Its statement is this. Let $q \geq 1$, let $\chi$ be a Dirichlet character modulo $q$, and let $s \in \mathbb{C}$ with $\operatorname{Re} s \neq 0$, $s \neq 1$ and $L(s, \chi) = 0$. Then $G_\chi(s) = 0$ or $L(1 - s, \bar\chi) = 0$. Here $G_\chi$ is the gamma factor of $\chi$ (Section 3). In Mathlib, $G_\chi(s) = 0$ exactly when $s$ is a pole of the classical gamma factor.

The theta series of the second file serve another part of the argument. Chapter 6 of this volume, [Pólya-Vinogradov and quadratic twists](/chapter/polya-vinogradov/), bounds the number of zeros of the twists $L(s, \psi\chi_K)$ near a point, through a mean value of $|L(1/2 + it, \chi)|$. Its starting point is an inequality that follows in two lines from the results of Section 4: for a primitive $\chi \neq \chi_0$ modulo $q$ of parity $j$ and $\operatorname{Re} z = 1/2$,
$$|\Gamma_j(z) L(z, \chi)| \leq 2\int_{q^{-1/2}}^\infty |\theta_\chi(u)|\, \frac{du}{u},$$
where $\theta_\chi$ is the theta series of $\chi$ and $\Gamma_j(z) = \Gamma_{\mathbb{R}}(z + j)/2$. The entire L-functions of the third file carry the poles of the transform in Landau's criterion (Volume 1, [the weighted prime remainder](/chapter/weighted-prime-remainder/)).

### A model: the zeta function

Riemann's proof of the functional equation of $\zeta$ has three steps (Davenport, *Multiplicative Number Theory*, Chapter 8). Let $\vartheta(x) = \sum_{n \in \mathbb{Z}} e^{-\pi n^2 x}$ for $x > 0$.

1. Poisson summation gives $\vartheta(1/x) = x^{1/2}\vartheta(x)$.
2. For $\operatorname{Re} s > 1$, integrate term by term: $\int_0^\infty \tfrac{1}{2}(\vartheta(x) - 1) x^{s/2}\, dx/x = \pi^{-s/2}\Gamma(s/2)\zeta(s) = \Lambda(s)$.
3. Split the integral at $x = 1$ and use step 1 on $(0, 1)$. The result is a formula for $\Lambda(s)$ that is visibly invariant under $s \mapsto 1 - s$, and that continues $\Lambda$ to $\mathbb{C}$ with simple poles at $0$ and $1$.

A zero $\rho$ of $\zeta$ with $0 < \operatorname{Re} \rho < 1$ is a zero of $\Lambda$, since $\Gamma_{\mathbb{R}}(s) = \pi^{-s/2}\Gamma(s/2)$ has no zero and no pole there. So $1 - \rho$ is a zero of $\Lambda$ and of $\zeta$. Also $\zeta(\bar s) = \overline{\zeta(s)}$, so $\bar\rho$ is a zero. The zeros in the strip form orbits under the group of order $4$ that $s \mapsto 1 - s$ and $s \mapsto \bar s$ generate. A zero off the line $\operatorname{Re} s = 1/2$ comes with a partner on the other side of the line.

For a Dirichlet character $\chi$ the same three steps work when $\chi$ is primitive. Two things change. The theta function of $\chi$ goes to the theta function of $\bar\chi$ under $x \mapsto 1/x$, with a factor $\tau(\chi)/q^{1/2}$ of absolute value $1$. And $s \mapsto 1 - s$ takes the zeros of $L(s, \chi)$ to the zeros of $L(s, \bar\chi)$. So the symmetry that keeps the character is the reflection $s \mapsto 1 - \bar s$ in the critical line.

### What the source adds

Mathlib has the functional equation for primitive characters. The source needs three things that Mathlib does not have.

1. The reflection of zeros for every character. Mathlib's $L(s, \chi)$ for an imprimitive $\chi$ is the imprimitive L-function, and the statements of the source quantify over all characters. Section 5 proves the reflection from the primitive case. The finite Euler factors that relate the two L-functions have zeros on the line $\operatorname{Re} s = 0$, and these zeros do not reflect. This is the reason for the hypothesis $\operatorname{Re} s \neq 0$.
2. The theta series of an arbitrary character, with a bound near $u = 0$ that does not need primitivity, and the transformation formula for a primitive character in absolute value. Section 4 proves these. The source does not prove the functional equation itself: it takes it from Mathlib.
3. The entire function $\tilde L(s, \chi)$, which is $L(s, \chi)$ or $(s - 1)L(s, \chi)$, so that every pole of $L'/L$ in $\mathbb{C}$ is a zero of an entire function (Section 2).

### The plan of the chapter

Section 2 defines characters, primitive characters and Gauss sums, the L-function and its continuation, the change of level, and the entire L-function. Section 3 defines the completed L-function, states the functional equation for a primitive character in the classical form and in the form of Mathlib, and derives a functional equation for every character. Section 4 is the theta series of the source. Section 5 proves the symmetry of the zeros: the classical form, the reflection theorem of the source, and the trivial zeros of every character. Section 6 has the exercises and the notes.

The chapter uses the identity theorem, Poisson summation for the Gaussian, Mellin transforms, and the non-vanishing of $L(s, \chi)$ on $\operatorname{Re} s \geq 1$ (Mathlib: `DirichletCharacter.LFunction_ne_zero_of_one_le_re`). It uses no result of a later chapter.

**Remark (Formalization).** The three files are short and classical. The file on zero symmetry has 82 lines and the file on theta series has 527. The list of references of the source puts the file on zero symmetry among the files whose citations were not compared with their sources. For the file on theta series it records Davenport and Montgomery and Vaughan, Chapter 10, as compared, with the place confirmed. Lean accepts these files if the checks that the source reports hold. This book did not rerun the checks (Volume 0, [the claim and its status](/chapter/claim-and-status/)).
