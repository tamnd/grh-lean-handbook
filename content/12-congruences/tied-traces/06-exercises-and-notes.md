---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $J = \{1, 2\}$. Write out the four coefficients $N(S)$ of $(\mathrm{Nm}_1 + X_1\partial_1)(\mathrm{Nm}_2 + X_2\partial_2)$. For $j = 2$ and $S = \emptyset$, find the element $N'$ of property 3 in [Norms at one prime](/chapter/tied-traces/#norms-at-one-prime).

*Hint.* $N(\emptyset) = \mathrm{Nm}_1\mathrm{Nm}_2$, $N(\{1\}) = \partial_1\mathrm{Nm}_2$, $N(\{2\}) = \mathrm{Nm}_1\partial_2$ and $N(J) = \partial_1\partial_2$. Take $N' = \mathrm{Nm}_1$. The subrings commute, so the order of the factors does not matter.

**Exercise 2.** Let $m = 7$ and $k = 2$, and let $v$ be $\mathrm{valMinAbs}$ on $\mathbb{Z}/7$. Put $f(x) = v(x)(v(x) + 2)$. Show that $f(x - 2) - f(x) + 4v(x)$ is a multiple of $7$ for every $x$. Find the $x$ for which it is not $0$.

*Hint.* If no reduction happens, $v(x - 2) = v(x) - 2$, and the expression is $(v - 2)v - v(v + 2) + 4v = 0$. A reduction happens only when $v(x) - 2 < -3$, that is, for $v(x) = -2$ and $v(x) = -3$. Then $v(x - 2) = v(x) + 5$. Use $f(y + 7) - f(y) = 7(2y + 9)$.

**Exercise 3.** Let $F = \mathbb{F}_3$, $N = 2$ and $g = \mathrm{diag}(2, 1)$. List the four lines of $F^2$ and the orbits of $g$ on them. Compute the transfer of the first entry at $g$ from the orbits, and compare it with $\det g$.

*Hint.* The lines of $(1, 0)$ and $(0, 1)$ are fixed, with scalars $2$ and $1$. The element $g$ swaps the lines of $(1, 1)$ and $(1, 2)$, and $g^2 = 1$, so this orbit gives $1$. The product is $2 = \det g$.

**Exercise 4.** Let there be two systems $x_1, x_2$, not congruent, and let $u \in \mathbb{T}$ with $u(x_2) = 0$ and $|u(x_1)| \geq 1$. Write out the congruence idempotent $A$ for $\pi = x_1$ and check its values.

*Hint.* Here $s = u$ and the only $y \sim \pi$ is $x_1$. So $A = 1 - (1 - u(x_1)^{-1}u)$, which is $u(x_1)^{-1}u$. Its values are $1$ at $x_1$ and $0$ at $x_2$. The bound $|u(x_1)| \geq 1$ makes $u(x_1)^{-1}$ integral.

**Exercise 5.** Let $\ell > n$ and $\ell \neq 2$. Show that a reduction modulo $\ell^\nu/(2n!)$ on an algebra $R$ over $\mathbb{Z}_\ell$ is the same as a ring map that kills $\ell^\nu R$.

*Hint.* Under these conditions $2n!$ is a unit in $\mathbb{Z}_\ell$. If $2n!\,x = \ell^\nu y$, then $x = \ell^\nu (2n!)^{-1}y$, so a map that kills $\ell^\nu R$ is a reduction. Conversely, if $x = \ell^\nu y'$, then $2n!\,x = \ell^\nu (2n!\,y')$, so a reduction kills $x$.

**Exercise 6.** Deduce from the corollary on the diamond element that $\mathrm{Nm}_j\cdot\mathrm{tr}[(\gamma_j - 1)g] = 0$, using only $\langle\gamma\rangle\,\mathrm{Nm}_j = \mathrm{Nm}_j$.

*Hint.* Take $f = 1$ and $p = 1$. Then the weighted sum is $\mathrm{Nm}_j$, the tame trace with $p = 1$ is $\mathrm{tr}[(\gamma_j - 1)g]$, and the right side has the factor $(\langle\gamma\rangle - 1)\mathrm{Nm}_j = 0$.

The exercises use only the statements of this chapter.

## Notes and references

For the congruence idempotent the source cites The Stacks Project, Tag 04GG, on the decomposition of a finite algebra over a henselian local ring into local rings, and [Tied traces](/chapter/tied-traces/#tied-traces) writes the idempotent down by hand. The auxiliary places, the diamond operators and the comparison of the tame generator with the determinant at principal level follow the method of R. Taylor and A. Wiles, *Ring-theoretic properties of certain Hecke algebras*, Ann. of Math. 141 (1995), in the form for $\mathrm{GL}_n$ of L. Clozel, M. Harris and R. Taylor, *Automorphy for some $\ell$-adic lifts of automorphic mod $\ell$ Galois representations*, Publ. Math. IHÉS 108 (2008). This chapter does not compare the statements of the source with these texts.

The notes and the plan have errors for this chapter. Research note F-180 puts EvenClasses, OnePrime and TiedTraces in the chapter [Auxiliary primes and first-order deformations](/chapter/first-order-deformations/). The `volume.yaml` of the volume puts them in this chapter. The note f-congr, §5, lists AuxiliaryPrimes under [Tied Selmer groups and the Greenberg-Wiles count](/chapter/tied-selmer-groups/), and `volume.yaml` puts it here. Plan 07.4 has an older list of the chapters of Volume 12 with no chapter on tied traces. The book follows `volume.yaml`.

One file of this chapter depends on a later chapter. TateTwistCocycles imports FittingBlock, which imports `New/Congruences/LocalLoss/Basic` of [The main summands of the attached Galois representations](/chapter/main-summands/). The chapter uses one definition from it, `crysRelations`. [Even classes and cocycles of Tate twists](/chapter/tied-traces/#even-classes-and-cocycles-of-tate-twists) states it once and links forward.

The chapter does not check that the source builds. It reports what the declarations state. Nothing in this chapter claims that the proof is correct or that the generalized Riemann hypothesis is proved.

Status: drafted by a model. No person has checked this chapter against the Lean source.
