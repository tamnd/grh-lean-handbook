---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Take $r = N = m = 1$ in [glued lattices](/chapter/comparison-operator-1/#glued-lattices). Write down the glue matrix for $\#a = 1$ and a unit $s$, and check by hand that it is block normalised. What changes when $s$ is divisible by the chosen place?

*Hint.* For $\#a = 1$ and $s$ a unit, take $D = 1$ and $B = \varpi$, as in the example of that section. If $\varpi \mid s$, the Hermite form step of `New.Rows.DividedSplitting.exists_isGlued` must move a factor of $\varpi$ into $D$.

**Exercise 2.** In the theorem on isolation, `New.Data.norm_apply_one_le_of_forall_isPeak`, the hypothesis is asked at every peak, not only at $z$. Find the step of the proof that needs the peaks $z\,\mathrm{rot}(\theta)$ for $\theta \neq 0$. Could one take $K_\theta = K_0'$ for all $\theta$?

*Hint.* The circle mean of $W_\theta$ is what produces $F(z)\,m_u$. Each $W_\theta$ needs its own orthogonal kernel $K_\theta$, and the lemma on orthogonality pays $2\delta$ for the change from $K_\theta$ to $K_0'$.

**Exercise 3.** Show that the bound of isolation does not depend on $C$ or on $F$. Replace the peak by any point $z$ with $|F(y)| \leq \lambda|F(z)|$ for all $y$, with $\lambda \geq 1$. What is the new bound?

*Hint.* The peak property enters only through $|W_\theta| \leq 2|F(z)|$ and $F(z) \neq 0$. The answer is $(2\lambda b^{n_*} + 1)\delta$.

**Exercise 4.** Prove the lemma on one column, `New.exists_toPoly_eq_det_and_weylNormSq_le`, for $h = 1$, $a$ empty, $N = \{1, 2\}$ and one column $c$, by direct expansion of the $2 \times 2$ determinant. Identify the coordinates of $\xi$ and the Gram matrix of the Weyl module of one box.

*Hint.* For one box the Weyl module is the standard representation, the Gram matrix is the identity, and the coordinates are $\pm$ the entries of $Z$. The determinant is $\pm(x_1Z_{21} - x_2Z_{11})$, and the bound $|Z_{11}|^2 + |Z_{21}|^2$ is an equality.

**Exercise 5.** In the theorem on first factors, the size property is asked only when $\vartheta$ has no tame places. Find where a tame place would break the proof of size, and why integrality survives at all primes coprime to $N(Q)$.

*Hint.* Look at the datum $\Psi^{\mathrm{add}}$ and at the modulus $\varpi^2Q$ of the last two kernels. The integrality lemma for definite kernels only asks that $\mathfrak{m}$ contain $qM^2$ with $p$ coprime to $q$.

## Notes and references

**What this part proves.** This part collects the tools of the comparison operator: the divided and glued lattices, the descent of product forms, the sparse theta kernels, isolation at a peak, the line coordinates $\zeta$ and the first factors. The [comparison operator, part 2](/chapter/comparison-operator-2/) assembles them into the statement that products span.

**Results that this chapter does not use.** Two passages of [single theta lifts](/chapter/single-theta-lifts/) send the reader to this chapter for results that its files do not contain or use. This chapter states them once, with links.

- The descent of a form is $0$ if and only if the form is orthogonal to the range of the lift (`New.Data.normalizedDescent_eq_zero_iff`). It is proved in [single theta lifts](/chapter/single-theta-lifts/) and used in [the comparison operator, part 2](/chapter/comparison-operator-2/).
- The twist factor `New.Rows.twistFactor` is not $0$ (`New.Rows.twistFactor_ne_zero`). Both are in [the comparison operator, part 2](/chapter/comparison-operator-2/).

**The literature.** The source names three works as related to the first factors. T. Yang, *Theta liftings and Hecke L-functions*, J. reine angew. Math. 485 (1997), treats the rank-one case, where the lift is a scalar whose square modulus is an $L$-value. S. Böcherer and C.-G. Schmidt, *p-adic measures attached to Siegel modular forms*, Ann. Inst. Fourier 50 (2000), and M. Harris, J.-S. Li and C. Skinner, *The Rallis inner product formula and p-adic L-functions* (2005), treat integral theta data and twisting on a square block. The source proves integrality off the conductor and smallness without a twist. It does not identify the first factors with $L$-values. The reduction theory of the short basis is classical and is in [reduction theory](/chapter/reduction-theory/). The Hermite normal form over a Dedekind ring, used for the glued lattices, is standard.

**What differs.** The isolation argument uses only the reproducing formula for holomorphic functions and the decay of discrete series coefficients. It does not use Fourier expansions or a cusp. The norm of $\zeta$ comes from Hadamard's inequality, not from an explicit formula for the Gram matrix.

**Errors in the research notes.**

- [Single theta lifts](/chapter/single-theta-lifts/), section 3, says that this chapter uses `New.Data.normalizedDescent_eq_zero_iff`. No file of this chapter uses it. The user is `New/OneLift/ComparisonOperator/GluingMaps.lean`, which `volume.yaml` puts in the comparison operator, part 2.
- [Single theta lifts](/chapter/single-theta-lifts/), section 4, places `New.Rows.twistFactor` and `New.Rows.twistFactor_ne_zero` in this chapter. Both are in `GluingMaps.lean`, in the comparison operator, part 2.
- A research note says that `DefiniteKernelSize` defines `New.Rows.twoSidedSubst`. It is defined in `New/OneLift/ComparisonOperator/DeterminantProducts.lean`, which is in [the exchange identity, part 2](/chapter/exchange-identity-2/). `DefiniteKernelSize` only uses it.
- No file of this chapter imports a file that `volume.yaml` puts in a later chapter of the volume.
