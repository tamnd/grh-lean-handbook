---
title: Exercises
lean:
  - Lib/Analytic/ZeroSymmetry.lean
  - Lib/Analytic/DirichletTheta.lean
  - Lib/Analytic/EntireLFunction.lean
  - Lib/Cyclotomic/Voronoi.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $p$ be a prime and let $\chi_0$ be the principal character modulo $p$. Derive the identity $\Lambda(1 - s, \chi_0)(1 - p^{-s}) = \Lambda(s, \chi_0)(1 - p^{s - 1})$ of Section 3 from the functional equation of $\zeta$. Show that $\Lambda(1 - s, \chi_0) = \Lambda(s, \chi_0)$ is false. Find all $s$ with $\operatorname{Re} s = 0$ and $L(s, \chi_0) = 0$, and check that for none of them is $1 - s$ a zero of $L(\cdot, \chi_0)$.

*Hint.* $\Lambda(s, \chi_0) = \Gamma_{\mathbb{R}}(s)\zeta(s)(1 - p^{-s})$, and $\Gamma_{\mathbb{R}}(1 - s)\zeta(1 - s) = \Gamma_{\mathbb{R}}(s)\zeta(s)$. For $s \neq 0$ the point $1 - s$ lies on $\operatorname{Re} s = 1$ and is not $1$. For $s = 0$ the point $1 - s$ is the pole.

**Exercise 2.** Let $\chi$ be the character modulo $12$ induced by $\chi_4$. Show that $\tau(\chi, 3) = 4i$, while $\bar\chi(3)\tau(\chi) = 0$. Show that $\tau(\chi) = 2i$, so that $|\tau(\chi)| = 2 \neq 12^{1/2}$. Which step of the proof of the proposition on Gauss sums fails?

*Hint.* The units modulo $12$ are $1, 5, 7, 11$, and $e(3a/12) = i^{a}$. For $\tau(\chi)$, use $e(7/12) = -e(1/12)$ and $e(11/12) = -e(5/12)$. The step is the choice of $c \equiv 1 \bmod q_1$ with $\chi(c) \neq 1$, for $q_1 = 4$.

**Exercise 3.** Let $q \geq 1$ and $r = q^{-1/2}$. Show that the map $u \mapsto 1/(qu)$ is a bijection from $(0, r)$ onto $(r, \infty)$, and that $\int_r^\infty f(u)\, du/u = \int_0^r f(1/(qu))\, du/u$ for every measurable $f \geq 0$. Deduce the corollary on folding of Section 4 from the symmetry of the theta series. Where does the proof use that the integral over $(0, \infty)$ converges?

*Hint.* The derivative of $1/(qu)$ is $-1/(qu^2)$, and $(qu)\cdot 1/(qu^2) = 1/u$. Lean's integral of a function that is not integrable is $0$, so the splitting of the integral at $r$ needs integrability on both pieces.

**Exercise 4.** The trivial zeros lemma of Section 5 assumes $e \geq 1$.

(a) Let $q > 1$ and let $\chi$ be an even character modulo $q$. Show that Mathlib's formula gives $L(0, \chi) = 0$. Check this by hand for $\chi = \chi_0$ modulo $q$.

(b) Let $\chi$ be the character modulo $20$ induced by $\chi_4$. Show that $\chi$ is odd and that $L(0, \chi) = 0$. So the statement of the lemma with $e = 0$ is false.

*Hint.* (a) The gamma factor $\Gamma_{\mathbb{R}}(s)$ has a pole at $0$, and $q \neq 1$. (b) $L(0, \chi) = L(0, \chi_4)(1 - \chi_4(5)5^{0})$, and $\chi_4(5) = 1$. The reflection theorem does not apply at $s = 0$, since $\operatorname{Re} 0 = 0$.

**Exercise 5.** Let $\chi$ be a primitive character modulo $q$ and let $0 < \operatorname{Re}\rho < 1$. Prove that $L(s, \chi)$ at $\rho$ and $L(s, \bar\chi)$ at $1 - \rho$ have zeros of the same order. Then let $\chi$ be the character modulo $12$ induced by $\chi_4$, and let $s_k = (2k + 1)\pi i/\log 3$. Show that $s_k$ is a simple zero of $L(s, \chi)$.

*Hint.* For the first part, use the functional equation as an identity of meromorphic functions, and the fact that $G_\chi(s)$, $G_{\bar\chi}(1 - s)$ and $q^{s - 1/2}w(\chi)$ have no zero and no pole in the strip. For the second part, $L(s, \chi) = L(s, \chi_4)(1 + 3^{-s})$. The factor has a simple zero at $s_k$. Show that $L(s_k, \chi_4) \neq 0$ with the functional equation and the non-vanishing on $\operatorname{Re} s = 1$.

**Exercise 6.** Let $\chi_0$ be the principal character modulo $6$. Show that $\tilde L(1, \chi_0) = 1/3$. Then let $N = 1$, $d = 3$, and let $\chi$ be the character modulo $1$. Show that the quadratic twist of $\chi$ by $(\cdot/3)$ is the odd character $\chi_3$ modulo $3$ with $\chi_3(2) = -1$, and that $\tilde L(s, \chi_3) = L(s, \chi_3)$.

*Hint.* $\tilde L(1, \chi_0) = (1 - 1/2)(1 - 1/3)$. For the twist, use `New.quadTwist_apply`: the value at $n$ is $\left(\frac{n}{3}\right)$, and $\left(\frac{2}{3}\right) = -1$. The lemma that the twist is not principal gives the last claim.

## Notes and references

Dirichlet introduced characters and L-functions in 1837 to prove his theorem on primes in progressions. Davenport, *Multiplicative Number Theory*, treats characters and $L(1, \chi) \neq 0$ in Chapter 4, primitive and induced characters in Chapter 5, Riemann's functional equation of $\zeta$ in Chapter 8, and the functional equation of $L(s, \chi)$ for a primitive $\chi$ in Chapter 9, with Gauss sums and the proof by theta functions that Sections 3 and 4 follow. Davenport states the functional equation for $\xi(s, \chi) = (q/\pi)^{(s + a)/2}\Gamma((s + a)/2)L(s, \chi)$, as $\xi(1 - s, \bar\chi) = i^{a}q^{1/2}\tau(\chi)^{-1}\xi(s, \chi)$. Iwaniec and Kowalski, *Analytic Number Theory*, treat characters and Gauss sums in Chapter 3, the Poisson summation formula and theta functions in Chapter 4, and L-functions in general in Chapter 5.

Mathlib's theory of Dirichlet L-functions is built on Hurwitz zeta functions. It contains the continuation, the change of level, the gamma factor, the completed L-function, the root number and the functional equation for primitive characters, and the non-vanishing on $\operatorname{Re} s \geq 1$. It does not contain the reflection of zeros for imprimitive characters, the conjugate symmetry of $L(s, \chi)$, or the theta series of a character. The source adds the first and the third. Its theta series serve the bound of Chapter 6 of this volume, not the functional equation.

The file on theta series cites Davenport and Montgomery and Vaughan, *Multiplicative Number Theory I*, Chapter 10. The list of references of the source records these citations as compared, with the place confirmed. The file on zero symmetry cites Montgomery and Vaughan, Corollaries 10.3 and 10.8. The list records these as not compared, and this book has not compared them.

The results of this chapter are classical. The argument of the source proves that no Dirichlet L-function has a zero with $\operatorname{Re} s > 1/2$, and the reflection of Section 5 turns this into the statement on the critical line. This book does not claim that the argument is correct. Volume 0, [the claim and its status](/chapter/claim-and-status/), describes what has and has not been checked.

Status: drafted by a model. No person has checked this chapter against the Lean source.
