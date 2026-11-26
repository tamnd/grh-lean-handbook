---
title: Exercises
lean:
  - New/UpperBound/Objects/Columns.lean
  - New/UpperBound/Objects/LiftChains.lean
  - New/UpperBound/Objects/PoincareMap.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Show that $n_m = r + mt + 1$, so that $Y_m$, of rank $r + mt$, has rank $n_m - 1$. Show that every $n_j$ is even. For data with $m = 4$ and $r = 3^{10}$, compute $k$, $\varrho$, $n_0$ and $n_4$.

*Hint.* $n_m = (r + 1 - m) + m(t + 1)$. The number $k$ is even because $r$ is odd and $m$ is even, and $t + 1 = 5r + 1$ is even.

**Exercise 2.** Let $p \ge 3$ be a prime, and let $\gamma \in \mathrm{GL}_n(\mathbb{Z})$ have finite order with $\gamma \equiv 1 \pmod p$. Prove that $\gamma = 1$. Explain how this statement, in a unitary form over the ring of integers of $E$, gives the freeness lemma of Section 6.

*Hint.* Reduce to $\gamma$ of prime order $\ell$, and write $\gamma = 1 + p^a A$ with $A \not\equiv 0 \pmod p$. Expand $\gamma^\ell = 1$ by the binomial theorem and compare the terms modulo $p^{2a+1}$. For the unitary form, the stabiliser $\Gamma \cap gKg^{-1}$ is a finite group of integral matrices that reduce to $1$ at the chosen places, and the size condition on $p_i$ replaces $p \ge 3$.

**Exercise 3.** Show that the zero function is a chain datum for every twist. Let $\Psi$ be a chain datum for a twist $\vartheta$ with $Q \neq \emptyset$, and let $c \in \mathbb{Z}$. Show that $c\Psi$ is a chain datum. What fails when $Q = \emptyset$?

*Hint.* The glued tensor is linear in $\Psi$, and integrality away from $q$ is closed under multiplication by integers. The size bound $\sum_x |\sigma(\Psi(x))| \le M^{3fmn_m^2}$ is asked only when $Q = \emptyset$, and it is not closed under scaling.

**Exercise 4.** Let $F$ be a finite dimensional inner product space with an orthonormal basis $(y_i)$, linear in the second slot. For a conjugate linear form $\ell$ on $F$, show that the Riesz vector is $\sum_i \ell(y_i)\, y_i$. Deduce that, for an orthonormal basis $(y_i)$ of the principal forms on $Y_0$, $\mathcal{P}\varphi = \sum_i \mathcal{B}(\varphi, y_i)\, y_i$.

*Hint.* Compute $\langle y_k, \sum_i c_i y_i\rangle = c_k$.

**Exercise 5.** Let $z$ be an operator of finite order dividing $N - 1$ on a complex vector space $V$. Show that the kernel of $\sum_{i < N-1} z^i$ is the image of $1 - z$. Use this to show that a source form is ramified if and only if, for each $w \mid \pi$, it lies in the image of $1 - z_w$.

*Hint.* The operator $e = (N - 1)^{-1} \sum_{i} z^i$ is the projection onto the fixed vectors, and $1 - e$ is the projection onto the image of $1 - z$. The scalings at different primes commute.

**Exercise 6.** Let $\mathrm{br}$ and $\mathrm{br}'$ both satisfy the definition of a branching map in Section 7. Show that $\mathrm{br}' = c\,\mathrm{br}$ for a rational number $c$. Show that the restriction $\mathrm{res}$ changes by the same factor $c$.

*Hint.* Use property 3 for each of them over $\mathbb{C}$. Both matrices are integral and nonzero, so $c$ is a ratio of two nonzero integer entries.

## Notes and references

The objects of this chapter are those of the source, and the order follows the order of need in Theorem A. The chain of theta lifts between definite unitary groups follows the method of the seesaw of S. Kudla, *Seesaw dual reductive pairs*, in *Automorphic forms of several variables* (1984), as [Theorem A and its plan](/chapter/theorem-a-plan/) explains. For algebraic modular forms on definite groups, the source names B. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999). The freeness of small levels rests on the classical lemma of Minkowski on integral matrices of finite order, in the unitary form that the outline proves. The Riesz map is the Riesz representation theorem in finite dimension. This book has not compared the citations of the source with its statements.

Three files of this chapter import files of later chapters: Columns.lean imports the admissible coefficients of [the first seesaw identity](/chapter/seesaw-identity-1/), PoincareMap.lean imports the grading of $Y_k$ from the same chapter, and CharactersAtLevel.lean reaches the scalings of [the gain of short columns](/chapter/short-columns-gain/) through [the chain valuation](/chapter/chain-valuation/). Each of these is stated once in this chapter, with a link to its home. The reader who follows the volume in order meets the three notions first here, and then again, with their proofs and uses, in the later chapters.

The remarks of Sections 2 and 7 concern nonvanishing. The source proves that the target forms are nonzero in a later volume. It does not prove in this chapter that a composite lift is nonzero, and the definition of a chain datum allows $\Psi = 0$.

Status: drafted by a model. No person has checked this chapter against the Lean source.
