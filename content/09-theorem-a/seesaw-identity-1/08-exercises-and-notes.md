---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

1. (Section 2.) Let $\sum_j c_j S(y_j)$ be an admissible combination of the values of $S$, and let each $S(y_j)$ be an admissible combination $\sum_k d_{jk} S'(y'_{jk})$ of the values of $S'$. Show that the composite is an admissible combination of the values of $S'$, and that its bound on the absolute sum of the coefficients is the product of the two bounds. *Hint.* Use the triangle inequality under each automorphism of $\mathbb C$.

2. (Section 3.) Let $s = 1$ and let the frame span the glued lattice with $\pi$ split squarefree for $N$ and $P$. Use the description of $\Lambda^+$ in Section 3 to show that $\Lambda^+/\Lambda^-$ is $N^{-1}\hat{\mathcal O}/\hat{\mathcal O}$ on the line of the string vector, and compute the order of its component at a place of $P$. *Hint.* $\pi$ is a uniformizer at $w \in P$ and a unit at $\bar w$.

3. (Section 5.) Prove part 2 of the lemma on products of constant terms from the relation between the constants of $\mathsf{Y}$ and $\mathsf{Y}'$. Where is the sign of the form on $V^-$ used? *Hint.* Compute $\mathrm{sh}\,\mathrm{sh}^*$ and $\mathrm{sh}'^*\mathrm{sh}'$ on each string vector of $V'$.

4. (Section 5.) In the proof of the double unfolding, find the place where $s$ odd is used. What goes wrong for even $s$ when the character of $W$ and the character of the kernel are compared on the unipotent group? *Hint.* Look at the grade of the middle vector of the string of $V$, and at the lemma `New.Seesaw.mul_constTermAtStringMap_unipotent_mul`, whose hypothesis is that $s$ is odd.

5. (Section 6.) In the proof of the vanishing at split points, the sum over $0 \leq i < N - 1$ is divided by $N - 1$. Where does the proof use that $z_w$ has order $N - 1$ modulo $w$, and where does it use only that $z_w^{N-1}$ acts trivially on the source forms? *Hint.* Compare `New.Data.ramifiedSourceForms` with `New.Data.centralRep_scalingGenerator_pow_eq_one`.

6. (Section 7.) Let $H = \mathbb Z/4$, $S = H$, $A = J = 0$ and $T = \{0, 1\}$. Show that the cover multiplicity is $2$ at every element of $H$, and that $\sum_{t \in T} m(t)^{-1} = 1$, the number of $S$-orbits in $H$. Then take $S = \{0, 2\}$ and compute the same sum. *Hint.* $t$ is covered by the translate $r + T$ exactly when $t - r \in T$.

## Notes and references

The unfolding in stages repeats, once for each lift of a chain, the classical global computation for one theta lift: the period of a theta lift along a Bessel or Fourier-Jacobi subgroup is computed by unfolding the theta series and keeping one orbit. The source names as related work B. Wang, *Global theta lifting and automorphic periods associated to nilpotent orbits*, and its REFERENCES file records that this citation was compared and its place confirmed. The seesaw principle used in the double unfolding of Section 5 goes back to Kudla, *Seesaw dual reductive pairs*, Progr. Math. 46 (1984). The REFERENCES file records that the work was found but gives no place in it. One step of unfolding, with its proof, is in [Bessel periods](/chapter/bessel-periods/), and the seesaw pairs are in [theta lifts and seesaws](/chapter/theta-lifts-seesaw/).

The treatment here differs from the classical one in two ways. First, every unfolding is done with an explicit finite datum, and the evaluation after each pair records the datum as a vector of the Weil representation of the definite spaces. This is what makes the denominators visible. Second, the integral over each outer variable is replaced by a finite sum over classes, with weights $m^{-1}$ that divide powers of the norm of the conductor of $\vartheta$. The source names as related work on denominators of this kind Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), Hsieh and Namikawa (2015), and X. Zhang (2022). This book has not compared these citations with the statements of the source.

The comment of the source on `New.Grading.inclXFin_mem_stdLevel` relates the glued level of Section 3 to Nikulin's criterion for extending isometries to an overlattice: the congruence on $h$ plays the part of the condition that an isometry preserves the gluing. See V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, Izv. Akad. Nauk SSSR Ser. Mat. 43 (1979). The Lean proof does not use this criterion; it computes with the glued basis directly.

**Remark (Formalization).** Three constants of this chapter are given by existence statements and are not shown to be nonzero: $\zeta_D$ of the double unfolding, $\kappa$ of the integral over a cut, and the linear forms $l$ of the evaluation after each pair. They combine into the constant $c$ of the seesaw identity in [part 2](/chapter/seesaw-identity-2/), and the identity has content only for $c \neq 0$. This chapter states only what Lean states.
