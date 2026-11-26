---
title: What the chapter proves
lean:
  - New/Determinant/AuxiliaryForms/RegularParameters.lean
  - New/Determinant/AuxiliaryForms/GridFirstColumns.lean
  - New/Determinant/AuxiliaryForms/Turns.lean
  - New/Determinant/AuxiliaryForms/DiagonalTurns.lean
  - New/Determinant/AuxiliaryForms/LastPath.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter is part of the proof of Theorem C. [The plan of Volume 11](/chapter/theorem-c-plan/) gives the four inputs of that proof. The first input is a family of auxiliary forms with a scalar $\gamma(\vartheta)$ whose absolute value is $\mathrm{Nm}(Q)^{e/2}$ times a product of turn ratios. This chapter moves a period through two grids of unitary groups, one square at a time, and computes the constant of each step. The next chapter, [deep level Poincaré series and spanning forms](/chapter/deep-level-poincare/), uses the results to build the forms.

### The setting from chapter 7

[Seesaw squares and grid paths](/chapter/seesaw-squares/) has all the objects that this chapter uses. Its Section 6 has the grid paths, the two-grid paths, the turns and the turn induction (GridPaths.lean). Its Section 7 has the nodes $(z, a, b)$, the spaces $Y^a_b$ and $\tilde Y^b_a$, the moduli $\mathfrak{m} = \mathfrak{b} Q$, $\mathfrak{m}_0 = \varpi Q$ and $\mathfrak{b} = \varpi^{b_0}$, the edge tuples, the path data, the period $I(\Psi; g)$ of a path and the relation $\Psi \propto \Xi$ (PathData.lean). We use these names without a new explanation. Its Section 5 has the one square identity, which gives the constant of a turn off the diagonal.

### The picture

The figure shows the grid of the $Y$ for $m = 3$. The node $(a, b)$ is the space $Y^a_b$. A half of a two-grid path starts at $(0, m)$, makes steps down (in $b$) and steps right (in $a$), and stops at a diagonal node $(l, l)$. The grid of the $\tilde Y$ has the same shape, and the two halves meet at the same $l$.

```text
        a=0      a=1      a=2      a=3
 b=3   (0,3)====(1,3)====(2,3)====(3,3)   last path
         |
 b=2   (0,2)    (1,2)    (2,2)
         |
 b=1   (0,1)    (1,1)
         |
 b=0   (0,0)                              first path:
                                           column a = 0
```

The first path is the column $a = 0$ in both grids, with $l = 0$. Its spaces are $Y_m, \ldots, Y_0$ and $\tilde Y^m_0, \ldots, \tilde Y^0_0$. The last path is the row $b = m$ in both grids, with $l = m$. All of its spaces are positive definite.

A turn replaces two sides of a unit square by the two other sides. The node $(a, b)$ of the path is replaced by $(a + 1, b + 1)$, and the path gains the square $(a, b)$.

```text
  inner turn, a < b                diagonal turn
  (a,b+1) --> (a+1,b+1)            (j,j+1) --> (j+1,j+1)
     |            |                   |
     v            v                   v
  (a,b)   --> (a+1,b)              (j,j)
  old: down, then right            old: ends at (j,j)
  new: right, then down            new: ends at (j+1,j+1)
```

A turn of the half in the grid of the $\tilde Y$ at its corner $(a, b)$ has the node $s = (b, a)$. So the node $s = (i, j)$ of a turn tells the kind of the turn: $i < j$ is a turn in the grid of the $Y$, $i > j$ is a turn in the grid of the $\tilde Y$, and $i = j$ is a diagonal turn. There are $m^2$ turns from the first path to the last.

### The three steps

**Step 1. The first path.** A conjugate form on $Y_m$ and a form on $\tilde Y^m_0$ move down the first columns by iterated transposed theta lifts. Their period on $\tilde Y^0_0$ is a constant times the period of one path datum $\Psi^0$ on the first path (Sections 3 and 4).

**Step 2. The turns.** A path datum on a path gives a path datum on the turned path. Proportionality of periods goes back the other way, with a constant $c$ (Section 5). Off the diagonal the constant comes from the one square identity (Section 6). On the diagonal it comes from two seesaws and a reversal of the line (Section 7). Composed over the $m^2$ turns, the constant $c(\vartheta)$ has, up to a constant and a power of $\mathrm{Nm}(Q)$, the absolute value

$$\prod_{i < m} \prod_{j < m} \mathrm{turnRatio}_{ij}(\vartheta).$$

**Step 3. The last path.** On the last path all groups are definite. The forms are algebraic forms, and the period of every path datum is a constant times a finite sum $\Xi$, divided by the order of a finite general linear group (Sections 8 and 9). The sum $\Xi$ is a sum of a bounded number of terms of bounded size.

Section 2 is a tool for Step 3. It finds the weight $(\kappa, e)$ of a regular parameter and bounds the boxes of $\kappa$ and the power $e$.

The figure shows how the three steps join. The arrows to the right carry path data. The arrows to the left carry proportionality.

```text
  transposed chains          first path        last path
  period on Ytilde^0_0  =  C * I(Psi^0)        I(Psi) = beta*Xi/n
                              |   Psi^0  ---->  Psi
                              |   (m^2 turns, bound k)
                            I(Psi^0) = beta*Xi/(n*c)  <----
```

Here $n$ is `triangleGLCard false` $\vartheta$ $m$, the order of $\mathrm{GL}$ of the rank of $Y_m$ modulo $\mathfrak{m}_0$. The join of the three steps is in the next chapter.

### The files

| Section | File | Content |
|---|---|---|
| 2 | [RegularParameters.lean](lean:New/Determinant/AuxiliaryForms/RegularParameters.lean) | weights of regular parameters |
| 3, 4 | [GridFirstColumns.lean](lean:New/Determinant/AuxiliaryForms/GridFirstColumns.lean) | the first path |
| 5, 6 | [Turns.lean](lean:New/Determinant/AuxiliaryForms/Turns.lean) | turns, off the diagonal |
| 7 | [DiagonalTurns.lean](lean:New/Determinant/AuxiliaryForms/DiagonalTurns.lean) | diagonal turns, all turns |
| 8, 9 | [LastPath.lean](lean:New/Determinant/AuxiliaryForms/LastPath.lean) | the last path |

No file of this chapter imports a file of a later chapter of Volume 11. The docstring of LastPath.lean refers to SpanningForms.lean, of the next chapter, only in its prose.

### Two warnings

The constants in this chapter come from existence statements. Many of them are not shown to be nonzero. The constant $C$ of Step 1 and the constant $\beta$ of a proportionality may be $0$. Then the statements hold but carry no information. The constant $c(\vartheta)$ of Step 2 is a unit by its type. The places where this matters are marked by a remark.

The source writes `false` for the grid of the $Y$ and `true` for the grid of the $\tilde Y$. The forms that move in the grid of the $Y$ are conjugate forms. On the first columns, the transposed lifts on the $Y$ side are taken at the twist $\vartheta$, and those on the $\tilde Y$ side at the trivial twist $1$.
