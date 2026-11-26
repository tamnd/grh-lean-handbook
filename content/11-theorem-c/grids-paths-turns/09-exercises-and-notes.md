---
title: Exercises and notes
lean:
  - New/Determinant/AuxiliaryForms/LastPath.lean
  - New/Determinant/AuxiliaryForms/DiagonalTurns.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises and notes

### Exercises

**Exercise 1.** Let $N = 3$ and let $\kappa(1) = 2$, $\kappa(2) = 1$, $\kappa(3) = 4$. Compute the rows $\lambda_0, \lambda_1, \lambda_2$ of the diagram. Check the two rules of `diagramWeight_eq_add_succ` and `diagramWeight_eq_zero_of_le_succ`. Where do the four columns of height $3$ go?

*Hint.* $\lambda_i$ sums $\kappa(h)$ over $i < h < 3$. The columns of height $3$ are $\det^4$.

**Exercise 2.** Let $\lambda = (3, 1)$ be a highest weight of $\mathrm{GL}_2$. List the highest weights $\mu = (\mu_0)$ of $\mathrm{GL}_1$ with $\lambda_1 \leq \mu_0 \leq \lambda_0$. For each, give the strip $\gamma$ and the rest $\kappa_1$ of `exists_add_eq_of_interlace`, and check $e_0 = e + \kappa_1(1)$.

*Hint.* Write $\lambda$ as columns: one column of height $2$ and two of height $1$. A box can leave a column only from the bottom, and at most one box leaves each column.

**Exercise 3.** In the proof of the branching pairing, the exponent is $N(\tau) = \gamma_0(\tau) + e(\tau)$, with $\gamma_0$ the first row of the strip. Show that $|N(\tau)| \leq |\kappa| + |e(\tau)|$. Show by an example in rank $2$ that the first row of $\gamma$ can equal the first row of $\kappa$.

*Hint.* $\gamma \leq \kappa$ column by column, and the first row of $\kappa$ is one term in the sum of all rows.

**Exercise 4.** Let the last path have $m = 1$. Draw its two halves and list its two edges. Write $\Xi$ as a sum over tuples $S$ of two matrices. Which levels occur in the class count of the shape theorem, and which of them depend on $\vartheta$?

*Hint.* The product runs over $j < m + 1$ for $z$ false and over $j < m$ for $z$ true. Only the level on $Y_m$ is $J(\mathfrak{m})$.

**Exercise 5.** Suppose that the constant $\beta$ of the proportionality is $0$ for some real point $g$. What does the theorem then say about the period of $\Psi$ at $g$? What does it say about the periods on the first path, after the transfer of Section 7?

*Hint.* Proportionality with constant $0$ says that the period vanishes. A transfer multiplies constants, so the product is $0$ as well. No lower bound follows.

**Exercise 6.** The turn induction of Section 7 counts the $m^2$ turns from the first path to the last path. For $m = 2$, give one sequence of turns, with the position $(i, j)$ of each, and mark the diagonal turns.

*Hint.* Each turn adds one square of the $m \times m$ grid of squares. There are $m$ diagonal squares.

**Exercise 7.** Let $A$ be the identity matrix on $\mathbb{C}^d$, with the standard Hermitian norm as Gram norm. Prove $|v'^{T} A v| \leq \|v'\|\,\|v\|$ and find the case of equality. Explain why the lemma on duality pairings uses a vector $x$ with $\|x\| = \|v\|$ and not $v$ itself.

*Hint.* The pairing $v'^{T} A v$ is bilinear, but the Gram form is Hermitian. Here $x$ is the complex conjugate of $v$.

### Notes and references

The grids, the paths through them and the $m^2$ turns are a device of the source. The guide register lists this as finding F-106 (open): the guide cites no source for the combinatorics, and it is not known whether it is new. This chapter follows the source and does not settle the question.

The volume file and [the chapters of the volume](/chapter/theorem-c-plan/#the-chapters-of-the-volume) name the chapter "Grids, columns and turns", and this is its title. The plan in the notes and some link texts in other chapters, for example in [the four inputs](/chapter/theorem-c-plan/#the-four-inputs), say "grids, paths and turns". The two names refer to the same chapter.

[Seesaw squares and grid paths](/chapter/seesaw-squares/) names the two paths of a turn in the opposite order from the source of this chapter. Section 7 notes this at the composite of the turns.

The source files are [RegularParameters.lean](lean:New/Determinant/AuxiliaryForms/RegularParameters.lean) (Section 2), [GridFirstColumns.lean](lean:New/Determinant/AuxiliaryForms/GridFirstColumns.lean) (Sections 3 and 4), [Turns.lean](lean:New/Determinant/AuxiliaryForms/Turns.lean) (Sections 5 and 6), [DiagonalTurns.lean](lean:New/Determinant/AuxiliaryForms/DiagonalTurns.lean) (Section 7) and [LastPath.lean](lean:New/Determinant/AuxiliaryForms/LastPath.lean) (Section 8). The grid paths and the path data are in GridPaths.lean and PathData.lean, which [seesaw squares](/chapter/seesaw-squares/#path-data-and-periods) explains.

The chapter uses results of Volumes 4 to 6 and 9: algebraic forms on definite groups, Weyl modules and branching, the seesaw for periods and the definite lifts, and the plain sums over classes. The chapter has no forward imports: no result in it depends on a later chapter.

The results of the chapter are used in [deep level Poincaré series and spanning forms](/chapter/deep-level-poincare/). There SpanningForms.lean combines the first path, the transfer to the last path, and the shape of $\Xi$. The constants of this chapter come from existence statements and may be $0$. So the chapter alone gives identities between periods, not lower bounds.
