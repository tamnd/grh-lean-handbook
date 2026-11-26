---
title: Dirichlet L-functions in Mathlib
lean:
  - Statements.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Dirichlet L-functions in Mathlib

The three statements about characters use one function, `DirichletCharacter.LFunction`. This section unfolds it, shows by checked theorems that it is the classical continuation of $L(s, \chi)$, and names the points where it differs from what a reader can expect: the pole, the zeros of imprimitive characters on the line $\operatorname{Re} s = 0$, and the other function `LSeries`, which a reader must not confuse with it.

### The classical object

Let $\chi$ be a Dirichlet character modulo $q \geq 1$. For $\operatorname{Re} s > 1$ put $L(s, \chi) = \sum_{n \geq 1} \chi(n) n^{-s}$. The series converges absolutely there. If $\chi \neq \chi_0$, then $L(s, \chi)$ has a continuation to an entire function. If $\chi = \chi_0$, then $L(s, \chi_0) = \zeta(s) \prod_{p \mid q} (1 - p^{-s})$, which has a continuation to $\mathbb{C}$ with one simple pole at $s = 1$ (Davenport, Chapters 4 and 9; Apostol, Chapter 12). One way to see the continuation is the Hurwitz zeta function $\zeta(s, a) = \sum_{n \geq 0} (n + a)^{-s}$ for $0 < a \leq 1$. Sorting $n$ by its class modulo $q$ gives
$$L(s, \chi) = q^{-s} \sum_{r = 1}^{q} \chi(r)\, \zeta(s, r/q) \qquad (\operatorname{Re} s > 1),$$
and each $\zeta(s, a)$ has a continuation with one simple pole at $s = 1$ of residue $1$ (Apostol, Chapter 12). The poles cancel when $\sum_r \chi(r) = 0$, that is when $\chi \neq \chi_0$.

### The L-function in Mathlib

**Definition (Dirichlet L-function).** Let $N \neq 0$ and let $\chi$ be a character of level $N$ with values in $\mathbb{C}$. Then
$$\texttt{LFunction}\ \chi\ s = N^{-s} \sum_{j \in \mathbb{Z}/N\mathbb{Z}} \chi(j)\, \texttt{hurwitzZeta}(j/N \bmod 1,\ s).$$
Mathlib: `DirichletCharacter.LFunction` is defined as `ZMod.LFunction χ s`, and `ZMod.LFunction Φ s` is `N ^ (-s) * ∑ j : ZMod N, Φ j * hurwitzZeta (toAddCircle j) s`.

The words in this formula unfold as follows.

1. `ZMod.toAddCircle j` is the point $j/N \bmod 1$ of the circle $\mathbb{R}/\mathbb{Z}$, where $j$ is any integer in the class.
2. `HurwitzZeta.hurwitzZeta a s` is `hurwitzZetaEven a s + hurwitzZetaOdd a s`. Each part is built from a theta function by a Mellin transform, as in Section 2. The theorem `HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re` of Mathlib says: for $a \in [0, 1]$ and $\operatorname{Re} s > 1$, the series $\sum_{n \in \mathbb{N}} 1/(n + a)^s$ has the sum `hurwitzZeta a s`.
3. At $a = 0$ the term $n = 0$ of that series is $1/0^s = 0$, by the junk values of Lean. So `hurwitzZeta 0` is $\zeta(s, 1) = \zeta(s)$. Mathlib states this as `HurwitzZeta.hurwitzZeta_zero`. So the term $j = 0$ of the Mathlib formula is the term $r = q$ of the classical formula, and the two formulas are the same.

The Mathlib definition is the Hurwitz formula of the classical theory, taken as the definition on all of $\mathbb{C}$. As in Section 2, a reader does not have to check the continuation of the Hurwitz functions. The next theorem fixes the function.

**Theorem (Mathlib's L-function).** Let $N \neq 0$ and let $\chi$ be a character of level $N$ with values in $\mathbb{C}$.

1. For $1 < \operatorname{Re} s$, `LFunction χ s` is $\sum_{n \geq 1} \chi(n) n^{-s}$.
2. `LFunction χ` is complex differentiable at every $s$ with $s \neq 1$ or $\chi \neq 1$.

So `LFunction χ` is the classical $L(s, \chi)$ on $\mathbb{C}$ if $\chi \neq 1$, and on $\mathbb{C} \setminus \{1\}$ if $\chi = 1$.
Mathlib: `DirichletCharacter.LFunction_eq_LSeries`, `DirichletCharacter.differentiableAt_LFunction` and `DirichletCharacter.differentiable_LFunction`.

*Proof.* Item 1 is `LFunction_eq_LSeries`, which says `LFunction χ s = LSeries (χ ·) s` for $1 < \operatorname{Re} s$. The series converges absolutely there (`DirichletCharacter.LSeriesSummable_of_one_lt_re`), so `LSeries` is the classical sum. Item 2 is `differentiableAt_LFunction`, with the hypothesis `s ≠ 1 ∨ χ ≠ 1`. The classical continuation is holomorphic on the same set. That set is $\mathbb{C}$ or $\mathbb{C} \setminus \{1\}$, which is open and connected and contains the half-plane $\operatorname{Re} s > 1$. The identity theorem gives the last claim. $\square$

**Theorem (Modulus one).** For the character $\chi$ of level $1$, `LFunction χ = riemannZeta`.
Mathlib: `DirichletCharacter.LFunction_modOne_eq`.

The source uses this theorem to deduce the zeta statement from the statement about L-functions at $N = 1$.

**Theorem (Change of level).** Let $M \mid N$ with $M, N \neq 0$, let $\chi$ be a character of level $M$, and let $\chi \neq 1$ or $s \neq 1$. Then
$$\texttt{LFunction}(\texttt{changeLevel}\ \chi)\ s = \texttt{LFunction}\ \chi\ s \cdot \prod_{p \mid N,\ p \text{ prime}} \left(1 - \chi(p)\, p^{-s}\right).$$
Mathlib: `DirichletCharacter.LFunction_changeLevel`.

For $\operatorname{Re} s > 1$ this is the Euler product with the factors at the primes $p \mid N$, $p \nmid M$ removed. The factor at a prime $p \mid M$ is $1$, since $\chi(p) = 0$ there. The special case $M = 1$ is `DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta`: for $s \neq 1$, `LFunction 1 s` of level $N$ is $\zeta(s) \prod_{p \mid N} (1 - p^{-s})$.

**Theorem (Nonvanishing on the line one).** Let $N \neq 0$, let $\chi$ be a character of level $N$, and let $s$ satisfy $\chi \neq 1$ or $s \neq 1$, and $1 \leq \operatorname{Re} s$. Then `LFunction χ s` $\neq 0$.
Mathlib: `DirichletCharacter.LFunction_ne_zero_of_one_le_re`.

This is the classical theorem of Hadamard and de la Vallée Poussin for L-functions, with the absolute convergence on $\operatorname{Re} s > 1$. The source uses it only at the point $s = 1$, for $\chi \neq 1$, in the proof of [New.grh](/decl/New.grh/). Every other point of the half-plane goes through the main argument.

### Three points where a reader can go wrong

**Remark (Formalization).** At $s = 1$ and $\chi = 1$ the function `LFunction 1` has a value, since Lean functions are total. This value is junk: classically there is a pole. Mathlib states no theorem about it, and none of the statements depends on it. The half-plane statement excludes the point by its hypothesis `χ ≠ 1 ∨ s ≠ 1`. The two statements on the line exclude it by `s.re < 1`.

**Remark (Formalization).** Let $\chi$ be imprimitive, induced by a primitive $\chi^*$ of level $M$. By the change of level theorem, $L(s, \chi)$ is $L(s, \chi^*)$ times the factors $1 - \chi^*(p) p^{-s}$ for the primes $p \mid N$, $p \nmid M$. Such a factor vanishes where $p^{-s} = \chi^*(p)^{-1}$. Since $|\chi^*(p)| = 1$, these zeros lie on the line $\operatorname{Re} s = 0$, and there are infinitely many of them. For example, for the character `1` of level $2$, `LFunction 1 s` $= (1 - 2^{-s}) \zeta(s)$ vanishes at $s = 2\pi i k / \log 2$ for every $k \in \mathbb{Z}$. At $k = 0$ this is the point $s = 0$, where $\zeta(0) = -1/2$ and the factor is $0$. These zeros are true zeros of the classical imprimitive L-function, not junk values. They are the reason that the two statements on the line ask for $0 < \operatorname{Re} s$. The statement with $0 \leq \operatorname{Re} s$ would be false.

**Remark (Formalization).** The statements use `LFunction`, not `LSeries`. The two functions agree only on $\operatorname{Re} s > 1$. By definition `LSeries f s` is `∑' n, LSeries.term f s n`, where `LSeries.term f s 0 = 0` and `LSeries.term f s n = f n / n ^ s` for $n \geq 1$. In Lean, `tsum` of a family that is not summable is $0$ (`LSeries.eq_zero_of_not_LSeriesSummable`). In $\mathbb{C}$, summable means absolutely summable. Mathlib proves that the series of $\chi$ is summable at $s$ if and only if $1 < \operatorname{Re} s$ (`DirichletCharacter.LSeriesSummable_iff`). So `LSeries (χ ·) s = 0` at every $s$ with $\operatorname{Re} s \leq 1$. With `LSeries` in place of `LFunction`, the half-plane statement and the statements on the line would fail at every point of the strip $1/2 < \operatorname{Re} s < 1$. The name `LFunction` in Statements.lean is therefore load-bearing. A reader who checks one thing in the file can check this.

### The completed L-function

The statements do not use the completed function, but the source's deduction does. Mathlib defines the gamma factor
$$\texttt{gammaFactor}\ \chi\ s = \begin{cases} \Gamma_{\mathbb{R}}(s) & \text{if } \chi \text{ is even}, \\ \Gamma_{\mathbb{R}}(s + 1) & \text{if } \chi \text{ is odd}, \end{cases}$$
and a completed function `DirichletCharacter.completedLFunction`. The theorem `DirichletCharacter.LFunction_eq_completed_div_gammaFactor` says that `LFunction χ s` is the completed function divided by the gamma factor, if $s \neq 0$ or $N \neq 1$. The theorem `DirichletCharacter.IsPrimitive.completedLFunction_one_sub` is the functional equation for a primitive $\chi$: the completed function at $1 - s$ is $N^{s - 1/2}$ times the root number times the completed function of $\chi^{-1}$ at $s$. The root number `DirichletCharacter.rootNumber` is defined for every $\chi$, and the docstring of Mathlib says that it is junk for imprimitive $\chi$. The functional equation has the hypothesis `IsPrimitive χ`, so the junk does not enter. The source reduces an imprimitive character to a primitive one before it uses the equation ([from the half-plane to the line](/chapter/half-plane-to-line/)).

A primitive even character $\chi \neq 1$ also has a zero at $s = 0$: the completed function is entire and $\Gamma_{\mathbb{R}}$ has a pole at $0$. This zero is on the line $\operatorname{Re} s = 0$ as well, and the open strip of the statements excludes it.
