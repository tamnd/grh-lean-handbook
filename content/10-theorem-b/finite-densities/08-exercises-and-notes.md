---
title: Exercises
lean:
  - New/Spanning/Frames/TopFloor.lean
  - New/Spanning/Frames/FiniteShells.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $A$ be the unramified quadratic extension of $\mathbb{Q}_p$, with the volume that gives $R$ the volume $1$. Show that the modulus of $p$, as defined in [the lattice datum](/chapter/finite-densities/#the-lattice-datum), is $p^{-2}$, and not the normalized absolute value $p^{-1}$. Deduce that the gauge of scale $\alpha = p^e$ has the loss $\Lambda = 2p^{2e}$.

*Hint.* $R/pR$ is the residue field, with $p^2$ elements, so $pR$ has volume $p^{-2}$. The loss is $2/|\alpha|$.

**Exercise 2.** In the model case of [what the chapter proves](/chapter/finite-densities/#what-the-chapter-proves), let $J = p^cR$ with $c \ge 0$. Show that $[R : J] = p^{2c}$, and that the dyadic shell of index $t$ is empty unless $2^{t-1} < p^{2c} \le 2^t$ for some $c$. Show that each shell meets at most one value of $c$.

*Hint.* Use the filtration $R \supset pR \supset \dots \supset p^cR$; each step has index $p^2$. Two values $c < c'$ have indices in the ratio $p^{2(c' - c)} \ge 4 > 2$.

**Exercise 3.** Let $A$ be a finite product of local fields, each with a Haar measure. Show that the set of non-units of $A$ is a null set. Deduce that the junk value of `unitOrOne` does not change the integral in the theorem on Fourier inversion at the last entry ([the top floor](/chapter/finite-densities/#the-top-floor)).

*Hint.* An element is a non-unit if and only if one of its components is $0$. The Haar measure of the product is the product measure, and a point of a nondiscrete local field is null.

**Exercise 4.** Prove that the fibre pairing does not depend on the chosen element $l$: if $l^{-1}z = l'^{-1}z$ with $l, l' \in G^{(\varrho)}$, then $\int_H\langle S_p(kl), S_q(kl)\rangle\,dk = \int_H\langle S_p(kl'), S_q(kl')\rangle\,dk$.

*Hint.* $l'l^{-1}$ fixes $z$, so $l' = hl$ with $h \in H$. The measure on $H$ is right invariant. This is `New.Floors.PlaceData.fiberPairing_orbitPoint`.

**Exercise 5.** Let $\omega_1, \omega_2$ be heads with the same last entry, and write $\rho_{ab} = \rho_\pi(\omega_a, \omega_b)$. Show that $\rho_{ba} = \overline{\rho_{ab}}$, and use the theorem on continuity and positivity to show $|\rho_{12}|^2 \le \rho_{11}\rho_{22}$.

*Hint.* The fibre pairing is an integral of inner products, so it is hermitian in $(p, q)$, and the density is a real multiple of an integral of it. Take $R = ww^*$ for $w \in \mathbb{C}^2$. Then the $2 \times 2$ matrix of the $\rho_{ab}$, transposed, is positive semidefinite.

**Exercise 6.** At a finite place with $\#\kappa = 1$, the lemma that the fibre measures disintegrate does not apply. Explain why the slicing theorem of [the top floor](/chapter/finite-densities/#the-top-floor) still makes sense as a statement, and what goes wrong in its proof.

*Hint.* `New.Floors.Place.normFiberMeasure` is defined by `Classical.epsilon` in every rank. The proof uses a hyperbolic basis of the standard form on $A^\kappa$, which needs two vectors.

## Notes and references

**The source.** The seven files of this chapter are part of the folder `New/Spanning/Frames`. Like the other files of the folder, they point to other files of the source for related work and cite almost no literature (finding F-105 of the project notes). So this chapter cannot say whether the method of the finite densities is new or adapted from a known source. The question is open in the notes (Q-33).

**Constants.** The theorems on shells and decay use the hypotheses $r + 10^8n^4 \le k$ and $t + 10^{10}n^4 \le k$ of `FiniteShells` (finding F-091). How these sizes fit with the rank of the field and the conditions of the reduction is open in the notes (Q-26). This chapter states the hypotheses as the source states them.

**Classical background.** The modulus of a locally compact field, as the factor by which multiplication scales a Haar measure, is in Weil, *Basic Number Theory*, Chapter I. The self-dual Haar measure and the additive character of a local field are in Tate's thesis, reprinted as Chapter XV of Cassels and Fröhlich, *Algebraic Number Theory*. The circle method picture of the top floor, with a sphere sliced by its last coordinate and a character summed over that coordinate, is the local form of the singular series. This chapter uses no further result from the literature: the lattices, the masses and the depth bounds are proved from the definitions.

**Positivity.** [The main term](/chapter/main-term/) uses the positivity of the last entry density in two ways. The matrix of the densities of a family of heads with one last entry is positive semidefinite (`New.Filling.IsFillingData.posSemidef_lastEntryDensity`), and the densities bound the squared norms of class sums with one last entry (`New.Filling.IsFillingData.sum_mul_norm_sum_cosetAmplitude_sq_le_lastEntryDensity`).

**Real places.** The real companion of this chapter is [the chapter on real densities](/chapter/real-densities/). There the sizes are discs, the shells are defined by lengths, and the Bessel vector is the Bessel function of the discrete series ([Bessel functions at a real place](/chapter/bessel-real-place/)).
