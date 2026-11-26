---
title: Exercises and notes
lean:
  - New/Spanning/Unfolding/CutoffIntegral.lean
  - New/Spanning/RemainingTerms/FrameCount.lean
  - New/Spanning/RemainingTerms/FramesOverLattice.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises and notes

**Exercise 1.** Let $x$ be an algebraic integer of $E$ with $|\Phi_v(x)| < 1$ at every infinite place $v$. Show that $x = 0$. Use this to show that two different algebraic integers have images at distance at least $1$ in $\prod_v\mathbb C$.

*Hint.* The norm $\operatorname{Nm}x = \prod_v|\Phi_v(x)|^2$ is an integer of absolute value less than $1$.

**Exercise 2.** Let $\varrho = 1$, so the only row below the top index is $a = 0$. Write the formula of [the integral of a cutoff](/chapter/frame-counts/#the-integral-of-a-cutoff) for `S.unipotentCovolume` in this case, and check the exponent $k + 2(\varrho - a) = d_a + 1$ at $a = 0$.

*Hint.* Here $d_0 = 0 + (k + 1) + 0 = k + 1$. Compare with the factor at the top index of `S.frameScaleProd`.

**Exercise 3.** Let $P^*\mu$ be skew-hermitian and $\mu\alpha P = \delta\mu$. Verify directly, for $1 \times 1$ matrices, that $\sigma = \bar\delta\mu\alpha - \delta\bar\alpha\bar\mu - \bar\alpha\bar P\mu\alpha$ satisfies $\bar\sigma = -\sigma$ and $\sigma P = |\delta|^2\mu$.

*Hint.* From $\bar\mu P = -\bar P\mu$, the last term is purely imaginary. Expand $\sigma P$ and use $\alpha P\mu = \delta\mu$ twice.

**Exercise 4.** Let $L$ be a free module over $\hat{\mathcal O}$ and $L' \leq L$ of finite index. Show that $[L : ML] = [L' : ML']$ for a unit $M$ of $\mathbb A_f$ that is integral. What fails if $[L : L'] = \infty$, and how does Lean encode the infinite case?

*Hint.* Compute $[L : ML']$ in two ways. In Lean `submoduleIndex` is $0$ for an infinite index, so the cancellation needs $[L : L'] \neq 0$.

**Exercise 5.** In the proof of [frames over a lattice](/chapter/frame-counts/#frames-over-a-lattice), add the exponents $2$, $270n^3$, $366n^4$ and $2n^3(\varrho + ln + n\varrho)$. Show that the sum is at most $2000n^6(l + 1)$ for every $n \geq 2$, $l \geq 0$ and $\varrho < n$.

*Hint.* Expand the last term into $2n^3\varrho$, $2n^4l$ and $2n^4\varrho$. Each of the six terms is at most $n^6(l + 1)$ times $2$, $270$, $366$, $2$, $2$ and $2$.

**Exercise 6.** A frame set separates terms by their frames modulo moves. Show that the near terms at one label form a frame set. Which hypothesis of `S.IsNearTermAt` is used for the double coset?

*Hint.* The term is the chosen representative of its double coset $\mathsf U^0_c\gamma\mathsf U^0_{c'}$. See the third rigidity lemma of [shared vectors and moves](/chapter/frame-counts/#shared-vectors-and-moves).

## Notes and references

The weight at one real place uses two classical results. The first is the inequality of Ostrowski and Taussky on determinants of matrices with a positive definite hermitian part: A. Ostrowski and O. Taussky, "On the variation of the determinant of a positive definite matrix", *Indagationes Mathematicae* 13 (1951), 383 to 385. The Lean form is `New.ostrowski_taussky`, proved in this chapter. The second is Hua's integral over matrix space: L. K. Hua, *Harmonic Analysis of Functions of Several Complex Variables in the Classical Domains*, American Mathematical Society, 1963. Its Lean form is `New.lintegral_norm_det_add_inv_pow_le`, stated in [discrete series](/chapter/discrete-series/).

The rigidity fact of Exercise 1 is the base of three steps: the packing bound, the vanishing of short lattice columns, and the separation of frames. The unique coset of reduced points is a version of the triangular reduction used for unipotent groups in reduction theory; see [reduction theory](/chapter/reduction-theory/) for the background of this book.

The source describes the integral of a cutoff as a case of the covolume computation for Heisenberg radicals, with a fixed product Haar measure in place of Tate's self-dual measures. This chapter does not compare the constant `S.unipotentCovolume` with a covolume computed from Tate's measures.

The lattice of a link rests on Jacobi's identity between a primitive sublattice of a unimodular lattice and its orthogonal complement. Its Lean form `New.genIndex_det_orthogonal_mul_submoduleIndex_sq` is stated in [the other tools](/chapter/fitting-ideals/). The frame count is a three-round colouring argument. The rounds sort the terms by the matrix of products and the shared vectors, by the part in $A$, by the part in $X_0$, and by the lifts of the lattice. The indices $[d]$ and $[d']$ that the colourings use are at most $b^{2n^3f}$. These bounds are crude. They suffice because the gains of [the remaining terms](/chapter/remaining-terms/) are larger by a power of $b$. For the sizes of the constants see [the data and their sizes](/chapter/data-and-sizes/).

The plan of Volume 10 puts the files `ReducedPoints` and `Packing` in this chapter. The research note on spanning places them in [the anatomy of a term](/chapter/anatomy-of-a-term/). This book follows the plan.

The statements of this chapter are those of Lean. Lean accepts them, if the reported checks hold. The chapter makes no claim that the argument proves Theorem B or GRH.

Status: drafted by a model. No person has checked this chapter against the Lean source.
