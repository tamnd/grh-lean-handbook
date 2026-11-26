---
title: The half-plane and the line
lean:
  - Main.lean
  - New/Main.lean
  - Lib/Analytic/ZeroSymmetry.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The half-plane and the line

This chapter proves the last step of the proof. The argument of the rest of the book proves one statement: no Dirichlet L-function vanishes in the half-plane $\operatorname{Re} s > 1/2$, except at the pole of a principal L-function. This chapter deduces the five theorems of the source from that statement. The five theorems are the Riemann hypothesis in the form of Mathlib, a second form of it, the half-plane statement itself, and two forms of the generalized Riemann hypothesis on the critical line. The tool is the reflection of zeros under $s \mapsto 1 - s$. Mathlib has the functional equation only for primitive characters, so the chapter proves the reflection for every Dirichlet character. The step is classical and short.

### Why the argument gives a half-plane

The method of the source is a criterion of Landau type (Chapter 4 of this volume). A one-sided bound for a weighted sum over primes, with weights of one sign, gives an analytic continuation of a Dirichlet series to a half-plane $\operatorname{Re} s > \beta$. The continuation has no poles there, and the poles that it excludes are the zeros of the L-functions. So the criterion proves that the L-functions have no zeros to the right of $\beta$. It sees only a right half-plane. It gives no information about a zero with $\operatorname{Re} s < 1/2$.

The zeros to the left come from the functional equation. The model is the Riemann zeta function $\zeta$. Let $\Lambda(s) = \pi^{-s/2}\Gamma(s/2)\zeta(s)$. Riemann proved that $\Lambda(1 - s) = \Lambda(s)$. Suppose that $\zeta(\rho) = 0$ with $\rho = \beta + i\gamma$ and $0 < \beta < 1/2$. The factor $\pi^{-s/2}\Gamma(s/2)$ is finite and not zero at $\rho$ and at $1 - \rho$, so $\Lambda(\rho) = 0$, so $\Lambda(1 - \rho) = 0$, so $\zeta(1 - \rho) = 0$. The real part of $1 - \rho$ is $1 - \beta > 1/2$. So the half-plane statement excludes $\rho$. A zero to the left of the line has a partner to the right of the line, and the half-plane statement excludes the partner.

Here is a picture in words. Draw the critical strip $0 < \operatorname{Re} s < 1$. The map $s \mapsto 1 - s$ is the half-turn about $1/2$, and $s \mapsto 1 - \bar s$ is the reflection in the line $\operatorname{Re} s = 1/2$. Both preserve the zeros of $\zeta$ in the strip. For a Dirichlet character $\chi$ that is not real, the half-turn takes the zeros of $L(s, \chi)$ to the zeros of $L(s, \bar\chi)$, and only the composite keeps the character. The half-plane statement is about all characters at once. So the deduction in the source uses only the half-turn, and it applies the half-plane statement to $\bar\chi$ as well as to $\chi$.

### What the chapter uses

The chapter uses the definitions and three theorems of Mathlib: the functional equation for a primitive character, the formula for an induced character, and the formula $L = \Lambda / \Gamma$. It also uses the half-plane statement, as a hypothesis. The book proves it in [the main inequality and the end of the proof](/chapter/main-inequality/). So this chapter does not depend on any other chapter of the book.

### The plan

Section 2 defines the objects. Section 3 states the four propositions that the source takes from Alpöge's original proof, and the half-plane theorem. Section 4 does the model case, the zeta function. Section 5 proves the reflection for every Dirichlet character. Section 6 makes the deduction and proves the five theorems. Section 7 has the exercises and the notes.

The proof for a character $\chi$ modulo $q$ and a zero $s$ in the strip has three steps.

1. The character $\chi$ is induced by a primitive character $\chi^*$ modulo a divisor $q^*$ of $q$. Then $L(s, \chi) = L(s, \chi^*) \prod_{p \mid q} (1 - \chi^*(p) p^{-s})$. Each factor of the finite product has its zeros on the line $\operatorname{Re} s = 0$. So $L(s, \chi^*) = 0$.
2. The functional equation of $\chi^*$ relates the completed L-function at $1 - s$ for $\bar\chi^*$ to the completed L-function at $s$ for $\chi^*$, by a factor that has no zero. In the strip the gamma factors have no poles. So $L(1 - s, \bar\chi^*) = 0$, and by step 1 again, $L(1 - s, \bar\chi) = 0$.
3. The half-plane statement at $(\chi, s)$ gives $\operatorname{Re} s \leq 1/2$. At $(\bar\chi, 1 - s)$ it gives $1 - \operatorname{Re} s \leq 1/2$. So $\operatorname{Re} s = 1/2$.

Three points need care, and the chapter spends most of its length on them. The first is the finite Euler factors, which have zeros on $\operatorname{Re} s = 0$. They are the reason that the reflection theorem asks $\operatorname{Re} s \neq 0$. The second is the poles of the gamma factor. At these points the L-function has its trivial zeros, and these zeros do not reflect. The third is a convention of Mathlib: $\Gamma_{\mathbb{R}}$ has the value $0$ at each of its poles. With this convention the formula $L = \Lambda / \Gamma$ holds at almost every point.

Lean accepts the five theorems if the checks that the source reports hold. This book did not rerun the checks (Volume 0, Chapter 2).
