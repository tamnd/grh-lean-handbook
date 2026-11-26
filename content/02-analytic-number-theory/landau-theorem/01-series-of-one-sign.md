---
title: Series of one sign
lean:
  - Lib/Analytic/Landau.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Series of one sign

This chapter gives the background for one tool of the proof: Landau's theorem on Dirichlet series and Laplace transforms with coefficients of one sign. The theorem says that such a transform has a singularity at the real point of its abscissa of convergence. So the half-plane of convergence is decided by the real axis alone. The chapter states the classical theorem with its sources, proves its standard consequences, and then compares it with the form that the source proves. A remark on the formalization follows each difference between the two forms.

### Where the chapter sits

[The plan](/chapter/theorem-and-plan/) of the proof ends with a one-sided bound $R_{q_0}(y) \leq y^{-1/2 + \varepsilon}$ for the weighted prime remainder of [the weighted prime remainder](/chapter/weighted-prime-remainder/). [Landau's criterion](/chapter/landau-criterion/) in Volume 1 turns that bound into the absence of zeros of the L-functions modulo $q_0$ in the half-plane $\operatorname{Re} s > 1/2$. The tool of that step is [Theorem](/decl/New.IsPolar.landau/), Landau's lemma for polar functions. Volume 1 proves it in full, together with the lemmas of the source that lead to it ([Polar pairs and Landau's lemma](/chapter/landau-criterion/#polar-pairs-and-landaus-lemma)), and it proves the model case of the zeta function ([The model case](/chapter/landau-criterion/#the-model-case)). This chapter does not repeat those proofs. It gives the theory around them.

The neighbours of this chapter in Volume 2 are [Dirichlet L-functions and zero symmetry](/chapter/dirichlet-l-functions/), which treats the L-functions $L(s, \chi)$ and the entire functions $\tilde L(s, \chi)$, and [polar functions and the explicit formula](/chapter/polar-functions/), which defines the polar functions of the source and explains the residues of a transform of a prime sum. This chapter uses both and treats neither again. In particular, the definition of a polar function is in [Polar functions](/chapter/polar-functions/#polar-functions).

### The phenomenon

Two examples show what the theorem says. The series $\zeta(s) = \sum_{n \geq 1} n^{-s}$ has nonnegative coefficients. It converges exactly in $\operatorname{Re} s > 1$, and it has a pole at the real point $s = 1$. The series
$$\eta(s) = \sum_{n \geq 1} (-1)^{n - 1} n^{-s} = (1 - 2^{1 - s})\zeta(s)$$
has coefficients of both signs. It converges in $\operatorname{Re} s > 0$ and in no larger half-plane, since its terms do not tend to $0$ for $\operatorname{Re} s \leq 0$. But $\eta$ is an entire function: the zero of $1 - 2^{1 - s}$ at $s = 1$ cancels the pole of $\zeta$. So nothing happens to the function at the point $s = 0$ where the series stops converging. The coefficients of one sign make the difference. For them the series converges as far to the left as the function can be continued along the real axis.

The reason is the inequality
$$\Bigl|\sum_n a_n n^{-\sigma - it}\Bigr| \leq \sum_n a_n n^{-\sigma} \qquad (a_n \geq 0).$$
The real point $\sigma$ dominates the whole vertical line through it. A Taylor expansion at a real point to the right of the abscissa has coefficients $\sum_n a_n (-\log n)^k n^{-\sigma}$ of alternating sign, and at a real point to the left all terms of the expanded series have one sign. So the Taylor series can be summed in any order, and its convergence gives the convergence of the Dirichlet series. This is the whole proof (Section 3).

### Why the proof needs it

The proof of the source uses the theorem in the form of [Theorem](/decl/New.IsPolar.landau/). A one-sided bound $E(v) \leq e^{(\beta - 1)v}$ makes the function $K e^{\beta v} - E(v)e^v$ nonnegative on $v > 0$ for a suitable constant $K$. So it is the density of a positive measure, and its transform is $K/(s - \beta)$ minus the transform of $E$. Landau's theorem applies to this measure. The poles of the transform of $E$ at the real points have residues of the right sign, so the transform of the measure converges in all of $\operatorname{Re} s > \beta$, and the transform of $E$ has no pole there. For $E(v) = R_{q_0}(e^v)$ the poles are at the zeros of L-functions. So a one-sided bound for a prime sum excludes zeros. The one sign is not a sign of the coefficients of a Dirichlet series. It is the sign of a density that the bound makes positive.

### The notation

The notation is that of [Landau's criterion](/chapter/landau-criterion/). We write $s = \sigma + it$. For a positive Borel measure $\mu$ on $[0, \infty)$ and real $\sigma$,
$$F(\sigma) = \int_0^\infty e^{-\sigma v}\, d\mu(v) \in [0, \infty],$$
and $\sigma_c \in [-\infty, \infty]$ is the abscissa of convergence, the left end point of the set of $\sigma$ with $F(\sigma) < \infty$. For the form of the source, $\mu$ is a measure on $\mathbb{R}$, $X$ is a real function with $X \leq 0$, $S$ is the set of real $t$ such that $e^{tX}$ is $\mu$-integrable, and $M(s) = \int e^{sX}\, d\mu$. A polar function is a function $E$ on $\mathbb{R}$ with a residue function $r$, as in [Polar functions](/chapter/polar-functions/#polar-functions). Volume 1 calls the pair $(E, r)$ a polar pair.

### The plan of the chapter

Section 2 defines the abscissae of convergence of Dirichlet series and of Laplace transforms of positive measures, and proves that such a transform is analytic to the right of its abscissa. Section 3 states Landau's theorem in its classical forms, for Dirichlet series (Montgomery and Vaughan, *Multiplicative Number Theory I*, Theorem 1.7) and for Mellin integrals of functions of one sign (the same book, Lemma 15.1). It derives the forms that the applications need. Section 4 gives two classical applications: Landau's proof that $L(1, \chi) \neq 0$ for a real character $\chi$, and the principle that a one-sided bound for an error term excludes the poles of its transform. The second is the model of the use in the source. Section 5 compares the classical theorem with the lemmas of the source, proves the lemmas of the source that Volume 1 does not state, and lists what the argument of the source uses. Section 6 has the exercises and the notes.

The source claims that its form of the theorem is checked by Lean, and the checks that the source reports would confirm this. This book has not rerun the checks (Volume 0, Chapter 2).
