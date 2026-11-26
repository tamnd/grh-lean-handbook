---
title: What the chapter proves
lean:
  - New/Spanning/Frames/Lengths.lean
  - New/Spanning/Frames/Shells.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter is the common core of the local densities of layer 4. A local density is an integral at one place, over a position and two frames, of a product of two correlations of a cut Bessel function. The chapter does not compute a density. It proves the tools that bound a density, in the same words at a real place and at the ring of all finite places of a finite set. Two later chapters use the tools: [the chapter on the real places](/chapter/real-densities/) and [the chapter on the finite places](/chapter/finite-densities/). The place of the chapter in the proof of Theorem B is shown in [Theorem B and its plan](/chapter/theorem-b-plan/), which puts it in layer 4, after [the chapter on Bessel functions at a real place](/chapter/bessel-real-place/).

The source is the folder `New/Spanning/Frames`, eleven files with 7180 lines. The first file, `Lengths.lean`, has a guide to the whole folder in 13 steps (lean:New/Spanning/Frames/Lengths.lean#L15). This chapter follows the guide, but it treats only the steps whose files are in the folder of this chapter. Steps 4 to 6 (the finite places, the fixed vectors and the mass at a real place) are in other chapters.

### The space and the frame

Fix a place with a ring $A$, an involution $x \mapsto \bar x$ (the field `star`), a modulus $|\cdot|$ on the units and an additive character $\psi$. The space $V = A^{r}$ has a basis

$$e_0, \dots, e_{\varrho - 1},\quad x_1, \dots, x_k,\quad z,\quad e^*_{\varrho - 1}, \dots, e^*_0,$$

and a hermitian form $h$ with Gram matrix $J$ (`T.splitGram`). In $J$ the pairs $e_a, e^*_a$ are hyperbolic planes, and the middle block $x_1, \dots, x_k, z$ carries the Gram matrix of the form $T$ of the shape. The unitary group of $h$ is $\mathsf{G}$ (in Lean `T.G`). The *frame* is the sequence $f = (e_0, \dots, e_{\varrho - 1}, z)$ of $n = \varrho + 1$ vectors.

Each basis vector has a *level* and a *floor*. The vector $e_a$ has level $a$, the middle block has level $\varrho$, and $e^*_a$ has level $2\varrho - a$. Both $e_a$ and $e^*_a$ have floor $a$, $z$ has floor $\varrho$, and the $x_i$ have floor $\varrho + 1$. The source uses the following groups and quotients.

- $G^{(l)}$ (`floorGroup l`) is the group of the isometries that fix the basis vectors of floor below $l$.
- $R^{(l)}$ (`partialUnitriangularGroup l`) is, for $l \leq \varrho + 1$, the group of the isometries that are unitriangular on the first $l$ vectors of the frame.
- $U_{<l}$ (`unipotentBelow l`) is the group of the isometries that are unitriangular when every basis vector of floor at least $l$ gets the middle level $\varrho$.
- $Y^{(l)}$ is the space of the vectors orthogonal to $e_0, \dots, e_{l-1}$, modulo the span of these vectors. The vector $e_a$ lies in $Y^{(a)}$.
- $H$ (`besselH`) and $\mathsf{U}$ (`besselU`) are the Bessel subgroup and its unipotent part. $H$ is the top floor group $G^{(\varrho + 1)}$.

### The plan in one paragraph

A density is first written as an integral over a position $x$ and a point $g$ of a double integral over the two frames at $g$ and at $w_p^{-1} g$, where $w_p$ is the Weyl element of a *head* $p$, a sequence of units. The modulus of the double integral is bounded by its *majorant*, a product of two one-frame integrals. A weight made of *depths* separates the two frames by the Cauchy-Schwarz inequality. Each frame is then bounded by itself along the Heisenberg groups of the frame, with Plancherel's formula on quadrics at each floor. This gives the bound for one frame. A *gain* at a position is a small factor that the separated bound wins: from a frequency, from two different heads, or from a deep vector. Last, the positions are cut into *shells* by their height. On a shell the bound for one frame loses a power of the height, and the gain from depth pays for this loss.

### The steps of the guide

The guide of the source lists the steps in this order. The section of this chapter that treats each step is given in brackets.

1. Gauges, lengths of vectors and balanced frames ([sizes and lengths](/chapter/local-frames/#sizes-lengths-and-balanced-frames), [place data](/chapter/local-frames/#place-data-floors-and-gauges)).
2. A density is an integral over a position and two frames ([densities](/chapter/local-frames/#densities-as-integrals-over-two-frames)).
3. The sum over the shells ([gains and shells](/chapter/local-frames/#gains-and-shells)).
4. to 6. The finite places, the fixed vectors and the mass at a real place (other chapters).
7. Plancherel's formula on a quadric ([quadrics](/chapter/local-frames/#quadrics-and-plancherel)).
8. Depth, and a subspace of large rank that looks the same from both points ([depth](/chapter/local-frames/#depth)).
9. Deep vectors are rare, and long coordinates force depth ([depth](/chapter/local-frames/#depth)).
10. A position of large height has a deep vector after the head ([depth](/chapter/local-frames/#depth)).
11. One frame, along the Heisenberg groups ([one frame](/chapter/local-frames/#one-frame)).
12. A weight made of depths separates the two frames ([gains and shells](/chapter/local-frames/#gains-and-shells)).
13. The gains at one position ([gains and shells](/chapter/local-frames/#gains-and-shells)).

The guide says that steps 3 to 6 rest on the gains of step 13, and that steps 7 to 12 prepare those gains. So the logical order is 1, 7, 8, 9, 10, 2, 11, 12, 13, 3. This chapter uses that order.

### The final bound of the chapter

The last theorem of the folder is the sum over the shells, [Theorem](/decl/New.Floors.Gauge.lintegral_le_of_shells/). In words: let $f \leq$ the majorant, let $f$ have the gain $V e^s$ at every position when $e < 1$, and let the shells $S_i$ of height $2^i$ cover the support of $f$. Then

$$\kappa_j(p, q)\int f\,d\mathsf{M} \leq V\cdot\min(1, e)^r\cdot\Lambda^{4\cdot 10^8 n^4}\cdot\mathcal{N}(W).$$

Here $\kappa_j$ is the density of the heads, $\mathsf{M}$ the Haar measure of the group, $s$ the exponent of the depths, $r \leq s - 9\cdot 10^7 n^4$, $\Lambda \geq 2$ the constant of the gauge and $\mathcal{N}(W)$ a normalization that contains the squared $L^2$ norm of the correlation of $W$. The exact statement, with all hypotheses, is in [the last section](/chapter/local-frames/#gains-and-shells). Each constant in it is explicit in the source. The constants are large, for example $\Lambda^{4\cdot 10^8 n^4}$, but the proofs need only that they do not depend on the position or on the Bessel function.

### How to read the chapter

The chapter has many definitions, and most of them are integrals with conditions. A reader who wants only the structure can read this section, the definitions of [the section on densities](/chapter/local-frames/#densities-as-integrals-over-two-frames), and the statements of [the last section](/chapter/local-frames/#gains-and-shells). The sections on sizes, quadrics and depth supply the constants. The proofs in this chapter are outlines of the Lean proofs. They give the main step and the source of each constant, and they do not repeat the bookkeeping of sizes.

The source works with extended nonnegative reals ($[0, \infty]$, `ℝ≥0∞`) for most integrals, and with complex Bochner integrals only for the forms themselves. Where the difference matters, a remark says so.
