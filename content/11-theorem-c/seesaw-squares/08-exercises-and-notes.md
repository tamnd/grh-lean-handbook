---
title: Exercises and notes
lean:
  - New/Determinant/AuxiliaryForms/GridPaths.lean
  - New/Determinant/AuxiliaryForms/PathData.lean
  - New/Determinant/Exchange/OneSquare.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---

## Exercises

**Exercise 1.** Show that the column from $(0, m)$ to $(0, b)$ and the row $\mathrm{row}(m, a)$ have no squares. Then show that the squares of the first two-grid path form the empty set, and that the squares of the last two-grid path are all pairs $(i, j)$ with $i, j < m$.

*Hint.* A step down at first index $0$ contributes the squares $(i, b)$ with $i < 0$, so none. A row has no step down. For the last path use the clause $i, j < l$ with $l = m$.

**Exercise 2.** Show that every chain of turns from the first two-grid path to the last one has exactly $m^2$ turns.

*Hint.* By `Turn.squares_eq` in Section 6, each turn adds exactly one square, and that square is new. Count the squares at the two ends with Exercise 1.

**Exercise 3.** Let $\Gamma$ be a two-grid path of size $m$. Show that $\Gamma$ has exactly $2m$ edges, not only at most $2m$.

*Hint.* A grid path from $(0, m)$ to $(l, l)$ has $l$ steps right and $m - l$ steps down, and each step adds a new edge, since one index changes strictly along the path. Every edge of $\mathrm{half}(z)$ has both ends in grid $z$ (`eq_and_le_of_mem_edges`). So the edge sets of the two halves are disjoint.

**Exercise 4.** Show that $2$ is a sum of at most $2$ roots of unity, but not a sum of at most $1$ root of unity. Show that a sum of at most $N$ roots of unity has absolute value at most $N$.

*Hint.* A complex number of finite order has absolute value $1$. Use the triangle inequality on the multiset $s$.

**Exercise 5.** Let $\Psi$ be a path datum for $N$ and $w$. Let $g$ be an admissible node family and $S$ an edge tuple with $g \cdot S = S$. Show that $\Psi(S) = 0$ if $\varepsilon(g, w) \neq 1$.

*Hint.* Condition 2 gives $\varepsilon(g, w)\Psi(S) = \Psi(S)$.

**Exercise 6.** Let $\Psi$ be a path datum for $N$ and $w$, and let $\Psi'$ be a path datum for $N'$ and $w$. Show that $\Psi + \Psi'$ is a path datum for $N + N'$ and $w$. Deduce that $\Psi \propto \Xi$ and $\Psi' \propto \Xi$ give $\Psi + \Psi' \propto \Xi$.

*Hint.* For condition 3, use the fact that $\Psi(S) + \Psi'(S) \neq 0$ forces $\Psi(S) \neq 0$ or $\Psi'(S) \neq 0$. For condition 4, join the two multisets. For the period, the sum over $\mathrm{tuples}(\Gamma)$ is linear in $\Psi$. Take $\beta + \beta'$ at each $g$.

**Exercise 7.** Show that the relation $\Psi \propto \Xi$ holds for $\Psi = 0$ and every $\Xi$.

*Hint.* The period of $\Psi = 0$ is $0$, so take $\beta = 0$.

## Notes and references

The seesaw principle is due to Kudla, *Seesaw dual reductive pairs*, in Automorphic Forms of Several Variables, Progr. Math. 46 (1984) 244-268. The one square identity of Section 5 is a seesaw identity of this kind: the lifts through $A$ and through $A'$ agree on matched data, up to the exchange constant and a factor $\kappa$ free of the twist.

The docstring of [OneSquare.lean](lean:New/Determinant/Exchange/OneSquare.lean#L44) also names, as related work, a paper of Chan on period identities of CM forms on quaternion algebras (2020) and a paper of He on compositions of theta correspondences (2005). We give only the names and years that the source gives. The book does not compare them with this chapter.

The Fourier analysis of Section 3 is the standard Fourier analysis on a finite abelian group, here the additive group of matrices modulo $\mathfrak{m}$. Section 3 proves the Gauss sums of matrices that it uses.

The grid paths and turns of Section 6 are a combinatorial device of the source. The induction over turns adds one square at a time. The transfer of periods along turns is in [grids, columns and turns](/chapter/grids-paths-turns/).

The findings of the register that concern this chapter are these.

1. F-069: the constant $\kappa$ of the one square identity is not shown to be nonzero. So the square law may be the trivial law. See [constants that may vanish](/chapter/register-of-findings/#constants-that-may-vanish).
2. F-121: the lemma `ne_zero_of_squareCommutes` is never applied in the source. The argument applies only `ne_zero_of_chainCommutes`.
3. Q-06, whether the nonvanishing of $\kappa$ is recovered in every use, is open.
4. [The plan](/chapter/theorem-c-plan/#constants-that-may-vanish) says that the source uses the identity only to show that the squares of a triangle commute. The source also applies it in [Turns.lean](lean:New/Determinant/AuxiliaryForms/Turns.lean#L769), for a square of the grids.
5. The constant $\beta$ of the relation $\Psi \propto \Xi$ may be $0$, as Exercise 7 shows.

This chapter does not prove that the constants are nonzero.

Status: drafted by a model. No person has checked this chapter against the Lean source.
