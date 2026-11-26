---
title: The statement and its place
lean:
  - New/Congruences/FitTwistsExist.lean
  - New/Determinant/Twist/LongForms.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The statement and its place

This volume proves one theorem that the main argument uses. The theorem is `New.exists_isRegularFamily`, in [FitTwistsExist.lean](lean:New/Congruences/FitTwistsExist.lean#L517). It says that for all data $D$ there is a *regular family* of $m$-fold twists. The family has one twist $\theta(\kappa)$ for each pair $\kappa = (\ell, \iota)$ of a prime $\ell$ and a ring isomorphism $\iota : \mathbb{C} \to \overline{\mathbb{Q}}_\ell$. Regular means two things. First, for the first $m$ powers of each twist, the inverse ratios of twisted to untwisted Hecke $L$-values form a family of small height. Second, for the same powers, the orthogonal projections of integral forms to the spaces of theta lifts have small $\ell$-adic denominators, and the logarithms of these denominators add up over all primes to at most a fixed budget.

This chapter is the plan of the volume. It states the theorem exactly, it explains the budget, it states the main steps of the proof with all hypotheses, and it gives a map of the 53 files of the folder `New/Congruences`. The later chapters prove the steps. [The proof of the existence of regular families](/chapter/proof-of-regular-families/) puts them together.

### Where the theorem enters the argument

The argument of the source is a comparison of size and divisibility in a lattice of automorphic forms ([the theorem and the plan](/chapter/theorem-and-plan/)). The star inequality $m \cdot \mathrm{rem} \leq f a \log^5 b$ bounds the remainder of a weighted prime sum ([the plan in one page](/chapter/theorem-and-plan/#the-plan-in-one-page)). Its proof uses three theorems on one space of target forms, of dimension $d_T$. Theorem C says that independent target forms are long: a family of $n \geq (1 - 4/b^2) d_T$ independent target forms with index at most $\delta$ and covolume at most $c$ has
$$d_T(\mathrm{mainAmount} - 3 f a \log^4 b) \leq c + 2\delta .$$
[The section on Theorem C](/chapter/theorems-a-b-c/#theorem-c-long-forms) states it with the Lean name `New.Data.integral_forms_long`. Its proof needs a twist $\xi_\iota$ at each prime, and it applies the lattice inequality of [twisted lattices](/chapter/twisted-lattices/) once for each choice of twists. The twists come from this volume. The proof obtains them in one line ([LongForms.lean](lean:New/Determinant/Twist/LongForms.lean#L144)):

```lean
obtain ⟨θ, hθ⟩ := exists_isRegularFamily D
```

This is the only place where the main proof uses the theorem. Outside the folder `New/Congruences`, only two files import it: LongForms.lean, which imports the top file, and [TwistedValueHeights.lean](lean:New/OneLift/HeckeValues/TwistedValueHeights.lean#L1) of Volume 11, which imports the file of definitions SelmerHypotheses.lean.

Theorem C needs the twists for a reason of signs. The lattice inequality says that a family of vectors with small covolume must have large index or large height. The height term for the twists is the height of the quotient $Z(1)/Z(\theta(\iota))$ of two chain determinants. This height must be negative, about $-d_T\,\mathrm{mainAmount}$. A chain determinant is a product of $m$ Gram determinants of single theta lifts, times a scalar. So each single lift must lose little to $\ell$-adic denominators. The loss of one lift is the subject of [the height of one lift determinant](/chapter/lift-volume-height/) in Volume 11. That chapter proves the bound under the hypothesis that the family is regular, and this volume proves the hypothesis.

### Why congruences cost height

A Gram determinant of theta lifts is a covolume. Its $\ell$-adic size is the index of a lattice: the lattice of integral forms that lie in the space $Z$ of lifts, inside the lattice of projections to $Z$ of all integral forms. If every integral form has an integral projection to $Z$, the index is $1$. If some integral form $y$ has projection $\mathrm{pr}_Z\, y$ with denominator $\ell^e$, the index grows. A denominator of a projection is the same thing as a congruence. A form in $Z$ and a form orthogonal to $Z$ that are congruent modulo $\ell^e$ give an integral sum whose projection has denominator $\ell^e$. [A model case](/chapter/regular-families-plan/#a-model-case-congruences-and-denominators) makes this exact in rank two.

So the theorem asks the lifts at a good twist to have few congruences with the forms that are not lifts. The source does not compute these congruences. It bounds them by Galois cohomology. This is the method of Ribet: a congruence between a lift and a form that is not a lift gives a nonzero class in a Selmer group of a Galois representation attached to the lift. A twist that makes the Selmer groups short therefore makes the denominators small.

### The idea of the proof in four steps

1. *Finitely many representations.* The spaces of lifts, for every twist, lie in the span of forms that lift one of finitely many Hecke eigensystems. The set of eigensystems does not depend on the twist. For each eigensystem the source attaches an $\ell$-adic Galois representation, the *main summand*.
2. *Ribet's method.* If the twist $\vartheta$ is auxiliary and the main summands, twisted by the $\ell$-adic avatar of $\vartheta^{-1}$, have Selmer groups of length at most $e'_\ell$, then the projection to the lifts has denominator at most $\ell^{\beta_\ell}$ per dimension and per unit of rank, with an explicit $\beta_\ell$.
3. *The twisting theorem.* For each $\ell$ and $\iota$ there is one $m$-fold twist $\tau$ whose powers $\tau^1, \dots, \tau^m$ all have this property, for all main summands at once. The same twist makes the ratios of $L$-values barely divisible by $\ell$.
4. *The sum over primes.* The numbers $\beta_\ell \log \ell$ and $e'_\ell \log \ell$ add up over all primes to at most the budget and to at most $x_1$.

Steps 2 and 3 are deep. Step 2 is Ribet's method to first order, with a bound for the local loss above $\ell$. Step 3 is a twisting theorem in the style of Mazur and Rubin, with Stickelberger elements built from theta lifts. Step 4 is bookkeeping, and the source does it in full in the top file. This chapter does Step 4 completely and states Steps 1 to 3 exactly.

### The status of the claim

The source claims the theorem with no `sorry`, no new axiom and no `native_decide` in the folder. Lean accepts it, if the reported checks hold. This book did not rerun the checks. Nothing in this chapter is a claim that the proof is correct or that the generalized Riemann hypothesis is proved.

### What the chapter uses

The chapter uses the data and their sizes ([the data and its sizes](/chapter/data-and-sizes/), and [the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes)), the CM field $E$ and the twists ([fields, places and twists](/chapter/fields-places-twists/)), and heights of families indexed by pairs $\iota$ ([twisted lattices](/chapter/twisted-lattices/)). For the place of the theorem in the main proof it uses [Theorems A, B and C](/chapter/theorems-a-b-c/) and [the main inequality](/chapter/main-inequality/). From Volume 11 it uses only the definitions of single theta lifts and critical pairs ([twists, critical pairs and regular families](/chapter/twists-critical-pairs/)).

### The plan

Section 2 defines heights, twists and the ratios of $L$-values. Section 3 defines the denominators of projections, regular families and the budget, and it states the theorem. Section 4 does the model case: a lattice of rank two, and the classical link between congruences and Selmer classes. Section 5 defines every constant of the budget and proves that the constants fit the budget. Section 6 states the chain of the proof, from the twisting theorem and Ribet's method to the theorem, and gives the proof of the theorem from these steps. Section 7 is the map of the files. Section 8 has the exercises and the notes.
