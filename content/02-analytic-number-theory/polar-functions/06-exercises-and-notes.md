---
title: Exercises
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

1. Let $f$ be analytic at $\rho$ and not identically $0$ near $\rho$, with a zero of order $m$ at $\rho$. Show that $(z - \rho)f'(z)/f(z) \to m$ as $z \to \rho$. Then show that the same limit holds for the logarithmic derivative of Mathlib, which is $0$ where $f = 0$.
   *Hint.* Write $f(z) = (z - \rho)^m g(z)$ with $g(\rho) \neq 0$. The zeros of $f$ near $\rho$ are only $\rho$ itself, and the limit is taken over $z \neq \rho$.

2. Let $\psi_0$ be the principal character modulo $q > 1$. Find all zeros of $\tilde L(s, \psi_0)$ on the line $\operatorname{Re} s = 0$, with their orders. Show that the order at $s = 0$ is the number of primes that divide $q$.
   *Hint.* $\tilde L(s, \psi_0) = (s - 1)\zeta(s)\prod_{p \mid q}(1 - p^{-s})$, and $\zeta(0) = -1/2$. Two factors $1 - p^{-s}$ and $1 - p'^{-s}$ with $p \neq p'$ have a common zero only at $s = 0$, since $\log p/\log p'$ is irrational.

3. Let $0 < \beta \leq 2$ and $m \in \mathbb{N}$. Show that $E(v) = v^m e^{(\beta - 1)v}$ is polar if and only if $m = 0$.
   *Hint.* For $m \geq 1$ the transform is $m!/(s - \beta)^{m + 1}$ for $\operatorname{Re} s > 2$. For the bound $|E(v)| \leq Ce^v$ when $\beta = 2$, look at the case $m \geq 1$ first: it fails, and this already settles the case.

4. Let $E$ be polar with residues $r$. Show that $v \mapsto E(v + a)$ is polar for every $a \geq 0$, and find its residues.
   *Hint.* Substitute $v \mapsto v - a$ in the transform. The integral over $(0, a)$ is an entire function of $s$, and the residue at $\rho$ is multiplied by $e^{(\rho - 1)a}$.

5. Let $q = 1$ and $d = 7$. Show that the residue function of $v \mapsto R_1(e^v)$ is $r(s) = (\operatorname{ord}_s \zeta - \operatorname{ord}_s L(\cdot, \chi_{-7}))/(s(1 - s))$ for $0 < \operatorname{Re} s < 1$. Show that $r(x) \geq 0$ at a real $x \in (0, 1)$ if $L(x, \chi_{-7}) \neq 0$.
   *Hint.* There is one character modulo $1$. Use the theorem of Section 5, and $x(1 - x) > 0$.

6. In the example of Section 5, check that $L(0, \chi_{-7}) = 1$ from the formula $L(0, \chi) = -\frac1k\sum_{a = 1}^{k} a\chi(a)$ for a character $\chi \neq \chi_0$ modulo $k$. Then explain why the residue of $\Phi$ at $0$ is $-G_1(0)$ and not $r(0)$.
   *Hint.* The squares modulo $7$ are $1, 2, 4$. Near $0$, $G_1$ is analytic, so $G_1(s)/s$ has a simple pole with residue $G_1(0)$, and $1/(s - 1) \to -1$.

7. Prove the lemma of Section 4 that a two-sided bound kills the poles, in the case $E(v) = 0$ for $v \geq Y$. Then show by an example that an upper bound alone does not kill the poles.
   *Hint.* For the first part, the transform is an entire function. For the second, use $-e^{(\beta_0 - 1)v}$.

## Notes and references

Sections 2 and 3 follow H. Davenport, *Multiplicative Number Theory*, 3rd edition, revised by H. L. Montgomery, Graduate Texts in Mathematics 74, Springer, 2000: Chapters 1 and 4 for the Euler products and Dirichlet's theorem, Chapter 6 for the class number formula, Chapter 9 for the functional equation, Chapters 11 and 12 for the Hadamard product and the partial fractions of $L'/L$, Chapter 15 for the number of zeros, and Chapters 17 and 19 for the explicit formulas for $\psi(x)$ and $\psi(x, \chi)$. Other forms of the explicit formula are in H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I: Classical Theory*, Cambridge University Press, 2007, Chapter 12, and in H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53, 2004, Chapter 5, Section 5.5.

Section 4 has no textbook source for the definition, which is the source's own. The nearest classical frame is D. V. Widder, *The Laplace Transform*, Princeton University Press, 1941, Chapter II, Theorem 5b, and Landau's theorem as in Montgomery and Vaughan, Lemma 15.1. The source cites both for its Landau lemma `New.IsPolar.landau`.

Section 5 restates the theorem `New.isPolar_primeRemainder` of [the weighted prime remainder](/chapter/weighted-prime-remainder/), where its full proof is given. The criterion that uses it is in [Landau's criterion](/chapter/landau-criterion/), and the $L$-functions $\tilde L$ are in [Dirichlet L-functions and zero symmetry](/chapter/dirichlet-l-functions/).

The chapter found these points about the notes and the plan.

1. The claim that `New.isPolar_primeRemainder` uses $d \equiv 7 \bmod 8$ only to get $d \neq 2$ is correct (Section 5).
2. The residue formula is the true residue at every $s \neq 0, 1$, and it is correct at $s = 1$ by the junk value $0/0 = 0$ (finding F-039). It is not the residue at $s = 0$ in general: for $q = 1$, $d = 7$ the residue is about $1.384330$ and the formula gives $0$. The notes state the formula only in $\operatorname{Re} s > 0$ and do not mention either point. The argument is not affected.
3. The compact edition has a stronger `IsPolar` with an extra property on $\operatorname{Re} s \geq 1$, which the notes do not mention (Section 4).
4. The entry of this chapter in the plan of the volume lists no source files, though the definition `New.IsPolar` is in Lib/Analytic/EntireLFunction.lean.

The sign of the residues (finding F-077) is still to be checked by a person.

Status: drafted by a model; no person has checked it.
