---
title: Exercises and notes
lean:
  - Lib/Weil/Periods/Unfolding.lean
  - Lib/Weil/Periods/PointLattice.lean
  - Lib/Weil/Periods/DescentVanishing.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of Sections 2 to 7.

**Exercise 1.** Show that $x \mapsto \Lambda(x)$ induces a bijection from $G_f / K^{\circ}$ to the set of lattices of the form $\Lambda(x)$. Show that $g \in G_f$ carries $\Lambda(x)$ to $\Lambda(g x)$ through its matrix $x_f\, g\, x_f^{-1}$ in rational coordinates.

*Hint.* For the first part, use the criterion $\Lambda(x) = \Lambda(x')$ if and only if $x^{-1} x' \in K^{\circ}$. For the second part, compute $(x_f g x)^{-1} (x_f g x_f^{-1}) = (x_f x)^{-1}$.

**Exercise 2.** Let $A \subseteq P$ and $U$ be submodules of a module. Prove the modular law $(A + U) \cap P = A + (U \cap P)$.

*Hint.* For $a + u \in P$ with $a \in A$, the element $u = (a + u) - a$ lies in $P$.

**Exercise 3.** Take $q = 0$ and $k \geq 1$. Show that every $x \in G_f$ has the lattice bounds. Find the step of the proof of finiteness that fails.

*Hint.* Both inclusions have $0$ on one side. In the proof, $U = \bar{q}^{\,k} \Lambda(1)$ is $0$, which is not open, so the quotient by $U$ is not discrete.

**Exercise 4.** Show that $\Lambda^{-}(x) = \Lambda^{+}(x)$ if and only if $\Lambda(x)$ is the direct sum of $\Lambda(x) \cap X$ and $\Lambda(x) \cap X^{\perp}$. Show that in this case $\Lambda^{-}(x)$ is self-dual in $X^{\perp}$.

*Hint.* If $\pi(\Lambda(x)) \subseteq \Lambda(x)$, then $y = (y - \pi y) + \pi y$ splits each $y \in \Lambda(x)$. For the second part, use the duality between $\Lambda^{-}(x)$ and $\Lambda^{+}(x)$.

**Exercise 5.** In Section 7, show that $\psi_u \psi_v = \psi_{u + v}$ and $\overline{\psi_u} = \psi_{-u}$ as functions of a frame. Deduce that the functions on the product of circles that agree with some $\psi_u$ on all frames form a monoid that is closed under complex conjugation.

*Hint.* The sum $\sum_{i, j} u_{ij} x_{ij}$ is additive in $u$, and $\psi$ is a character with values of modulus $1$.

**Exercise 6.** Show that the block period satisfies $I(v h) = I(h)$ for every $v$ in the second block. Deduce that $I(h)$ depends only on the frame $h^{-1} o_1$.

*Hint.* For the first part, use the left invariance of the measure on $[U(n_2)]$. For the second part, if $h^{-1} o_1 = h'^{-1} o_1$, then $h' h^{-1}$ fixes $o_1$, so it lies in the second block.

## Notes and references

**Bessel and Fourier-Jacobi periods under theta lifts.** The step of Section 5 is a case of the transfer of periods attached to nilpotent orbits under a global theta lift. The source cites B. Wang, *Global theta lifting and automorphic periods associated to nilpotent orbits*, J. Number Theory 271 (2025), 122-149, Prop. 3.2 and Thm. 4.5, as the source of the method. The source treats only unitary pairs, hook orbits with a definite complement $X$, and one step at a time. It treats the Bessel and the Fourier-Jacobi cases together, through the parity of the length $s$ of the string.

For the local form of the transfer, the source cites R. Gomez and C.-B. Zhu, GAFA 24 (2014), 796-853. For unitary hooks it cites M. Furusawa and K. Morimoto, Math. Ann. 391 (2025), §3. The chapter does not compare its statements with these works beyond what the source says.

**Lattices and the Iwasawa decomposition.** The results of Section 6 are standard facts on unimodular hermitian lattices over the rings of integers of unramified local fields. The source cites O'Meara, *Introduction to Quadratic Forms*, and Jacobowitz, *Hermitian forms over local fields* (1962), for the duality of lattices and for Witt's theorem on unimodular hermitian lattices. For the finiteness of the lattices between two given ones and for the local nature of lattices, the source cites O'Meara, §81. The file with the finiteness theorem is in the list of files whose citations were not part of the comparison. For the Iwasawa decomposition the source cites J. Tits, *Reductive groups over local fields*, Proc. Sympos. Pure Math. 33 (1979), 3.3.2. The Witt theorem over $\hat{\mathcal{O}}$ that the source uses is the one of [the chapter on adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/).

**Fourier coefficients and descents.** The unfolding of Section 7 is the unfolding of a single nondegenerate Fourier coefficient of a theta lift by Witt's theorem. The source cites P. Walls, *The theta correspondence, periods of automorphic forms and special values of standard automorphic L-functions*, arXiv 1501.01565 (2015), Prop. 2.1.1, and S. Rallis, *On the Howe duality conjecture*, Compositio Math. 51 (1984), 333-399. The file with this unfolding is also in the list of files whose citations were not part of the comparison.

**Where the results are used.** The iteration of the step of Section 5, and the identification of the iterated function with the source function of Section 3, are in [seesaw identity, part 1](/chapter/seesaw-identity-1/). The finite sets of Section 6 give the stage cuts of the seesaw there. The vanishing of block periods of Section 7 is used in [false lifts](/chapter/false-lifts/). The place of both in the proof of the main theorem of the source is in [the theorem and the plan](/chapter/theorem-and-plan/). This chapter describes what the Lean source states. It does not claim that the proof of the source is correct.
