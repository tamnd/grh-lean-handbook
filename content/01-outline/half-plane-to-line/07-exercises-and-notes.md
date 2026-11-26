---
title: Exercises
lean:
  - Statements.lean
  - Main.lean
  - New/Main.lean
  - Lib/Analytic/ZeroSymmetry.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $\chi_0$ be the principal character modulo $6$. Write $L(s, \chi_0)$ as $\zeta(s)$ times a finite product. Find all zeros of $L(s, \chi_0)$ on the line $\operatorname{Re} s = 0$, and show that $s = 0$ is a double zero. Show that no zero on $\operatorname{Re} s = 0$, other than $s = 0$, has its partner $1 - s$ as a zero.

*Hint.* $L(s, \chi_0) = (1 - 2^{-s})(1 - 3^{-s})\zeta(s)$. The two progressions $2\pi i k / \log 2$ and $2\pi i k / \log 3$ meet only at $0$, since $\log 2 / \log 3$ is irrational. For the partners, use $L(s, \chi_0) \neq 0$ on $\operatorname{Re} s = 1$, $s \neq 1$.

**Exercise 2.** Let $\chi_3$ be the character modulo $3$ with $\chi_3(2) = -1$, and let $\chi$ be the character modulo $12$ that it induces. Find the parity of $\chi$, the factor $E(s)$ of Section 5, and the zeros of $L(s, \chi)$ on $\operatorname{Re} s = 0$. Check that the reflection theorem fails at each of these zeros if one drops the hypothesis $\operatorname{Re} s \neq 0$.

*Hint.* $\chi_3$ is odd, and $E(s) = 1 + 2^{-s}$. Compare the example modulo $12$ in Section 5.

**Exercise 3.** Show that the proof of the line statement in Section 6 applies the half-plane statement only at points $s$ with $1/2 < \operatorname{Re} s < 1$. Show that the proof of the zeta statement in Section 4 applies it also at points with $\operatorname{Re} s > 1$. Which classical theorem covers those points?

*Hint.* If $\operatorname{Re} s < 0$ then $\operatorname{Re}(1 - s) > 1$. The theorem is the non-vanishing of $\zeta$ on $\operatorname{Re} s \geq 1$, through the Euler product and the theorem of Hadamard and de la Vallée Poussin.

**Exercise 4.** Fix one character $\chi$. Assume that $L(s, \chi) \neq 0$ for every $s$ with $1/2 < \operatorname{Re} s < 1$. Prove that every zero of $L(s, \chi)$ with $0 < \operatorname{Re} s < 1$ has $\operatorname{Re} s = 1/2$. Do not assume anything about $\bar\chi$.

*Hint.* Use the corollary of Section 5 in place of the reflection theorem. Where does the proof use the conjugate symmetry?

**Exercise 5.** In the Lean statement of `New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero`, replace the hypothesis `s.re ≠ 0` by `0 < s.re`. Show that the weaker theorem still proves [Theorem](/decl/New.zeros_on_line/). Then find the one place in the source outside the last step that applies the theorem, and show that the weaker theorem is not enough there.

*Hint.* Search the source for the name of the theorem. The other place is `New.OddPart.LFunction_neg_nat_eq_zero_iff`, which finds the trivial zeros $L(-e, \chi) = 0$, $e \geq 1$, of every character. There $\operatorname{Re} s = -e < 0$, and the reflection with the non-vanishing on $\operatorname{Re} s \geq 1$ leaves only the poles of the gamma factor.

**Exercise 6.** Mathlib proves $L(s, \chi) = \Lambda(s, \chi) / G_\chi(s)$ for every $s$, except $s = 0$ when $q = 1$. Let $\chi_0$ be principal modulo $q > 1$. Show by hand that $L(0, \chi_0) = 0$, so that the formula at $s = 0$, which reads $L(0, \chi_0) = \Lambda(0, \chi_0)/0 = 0$, is true. Then compute $\Lambda(0, \chi_0)$ on paper.

*Hint.* By the change of level formula, $L(0, \chi_0) = \zeta(0) \prod_{p \mid q}(1 - 1)$. For $\Lambda(0, \chi_0)$, the zero of $L(s, \chi_0)$ at $0$ has order $\omega(q)$, the number of primes that divide $q$, and $\Gamma_{\mathbb{R}}(s) \sim 2/s$. The answer is $0$ if $\omega(q) \geq 2$, and $-\log p$ if $q$ is a power of a prime $p$.

## Notes and references

The functional equation of $\zeta$ is Riemann's (1859). The functional equation of $L(s, \chi)$ for a primitive $\chi$ is in Davenport, *Multiplicative Number Theory*, Chapter 9, with the proof by theta functions that Section 2 follows. Davenport states it for $\xi(s, \chi) = (q/\pi)^{(s + a)/2}\Gamma((s + a)/2) L(s, \chi)$, as $\xi(1 - s, \bar\chi) = i^a q^{1/2}\tau(\chi)^{-1}\xi(s, \chi)$. Mathlib's $\Lambda(s, \chi)$ has no factor $q^{s/2}$, and the factor $q^{s - 1/2}$ of Section 2 makes up the difference. The zeta case is in Chapter 8 of Davenport, and primitive and induced characters are in Chapter 5. Iwaniec and Kowalski, *Analytic Number Theory*, Chapter 5, treat L-functions in general: the gamma factor, the conductor, the trivial zeros, and the symmetry of the zeros that the functional equation gives.

The textbooks prove the functional equation for primitive characters and leave the imprimitive case to the Euler factors, as Section 5 does. The source states the main theorem for every character, with Mathlib's imprimitive L-function. This is why it needs the reflection for every character, which Mathlib does not have. The file on zero symmetry cites Montgomery and Vaughan, *Multiplicative Number Theory I*, Corollaries 10.3 and 10.8. The list of citations of the source puts this file among those whose citations were not compared, and this book has not compared them.

The step of this chapter is classical. The source proves the half-plane form because its method, a criterion of Landau type, gives that form (Chapter 4 of this volume).

Status: drafted by a model. No person has checked this chapter against the Lean source.
