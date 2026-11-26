---
title: Exercises and notes
lean:
  - Lib/Adelic/Reduction/FirstMinimumShortBases.lean
  - Lib/Adelic/Reduction/FiniteVolume.lean
  - Lib/Adelic/Reduction/DefiniteClassSums.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $E$ be imaginary quadratic, so $f = 1$, and let $V = I_1$. For $g = (u, h) \in G$, show that the base lattice of the moved space is a fractional ideal $\mathfrak{a}$ of $E$ with $\mathfrak{a} \bar{\mathfrak{a}} = \mathcal{O}_E$, and that the length of $\xi \in \mathfrak{a}$ is $|\xi|$. Deduce $\lambda(Vg) = 1$ without the orthogonality lemma of Section 5.

*Hint.* The ideal of $\xi \ne 0$ is $\mathfrak{a}$ times an integral ideal, so $|\xi|^2 = N(\xi) \ge N(\mathfrak{a}) = 1$. The unit $u$ has absolute value $1$.

**Exercise 2.** Let $\Lambda = \mathbb{Z}^m$ in $\mathbb{R}^m$, with $\rho = 1$. Compute the covering radius and the first minimum of $\Lambda$, and compare them with the bounds $m^2$ and $2m$ of weak transference. For which $m$ is the covering radius bound of Banaszczyk, $m/2$, sharp for this lattice?

*Hint.* The covering radius is $\sqrt{m}/2$, attained at $(1/2, \dots, 1/2)$. Compare $\sqrt{m}/2$ with $m/2$.

**Exercise 3.** Let $\Lambda = \mathbb{Z} + \sqrt{2}\,\mathbb{Z} \subset \mathbb{R}$. Show that no nonzero $y \in \mathbb{R}$ pairs integrally with $\Lambda$, so the hypothesis of weak transference holds for every $\rho > 0$. Check both conclusions directly. Explain why the proof of part (1) still works although $\Lambda$ is not a lattice.

*Hint.* $y \in \mathbb{Z}$ and $y\sqrt{2} \in \mathbb{Z}$ force $y = 0$. $\Lambda$ is dense in $\mathbb{R}$. The proof argues by contradiction, and the assumption that all nonzero vectors are long makes $\Lambda$ discrete.

**Exercise 4.** Let $q > 1$. Show that $\sum_{x \in \mathbb{Z}^n} \prod_i q^{-|x_i|} = \big((q + 1)/(q - 1)\big)^n$. In the proof of Weil's criterion, $q^2 = 2^f$. Find the factor that this sum contributes to the final bound when $E$ is imaginary quadratic.

*Hint.* The sum is a product of $n$ copies of $1 + 2\sum_{k \ge 1} q^{-k}$. For $f = 1$, $q = \sqrt{2}$.

**Exercise 5.** Let $E$ be imaginary quadratic and $V = I_1$. Use the theorem on class sums with $F = 1$ and $K = K_0$ to show $\operatorname{vol}(\Gamma_V \backslash G) = h_1/\#\mu_E$. Show that $h_1$ is the order of $E^1 \backslash \mathbb{A}_{E,f}^1 / \hat{\mathcal{O}}_E^1$, and that it is finite by the compactness theorem of Section 6. Compute $\#\mu_E$ for $E = \mathbb{Q}(i)$ and $E = \mathbb{Q}(\sqrt{-3})$.

*Hint.* The stabilizers are $E^1 \cap \hat{\mathcal{O}}_E^1$, a finite group of units of absolute value $1$. The answers are $4$ and $6$.

**Exercise 6.** Let $a, b$ be vectors of the base lattice of a space with $a^* J b \ne 0$. Show that $\|a\|_V \|b\|_V \ge 1$. Give an example in $I_2$ over $\mathbb{Q}(i)$ where equality holds.

*Hint.* This is the orthogonality lemma of Section 5. Take $a = b = e_1$, a vector of length $1$.

## Notes and references

The classical reduction theory is in A. Borel and Harish-Chandra, *Arithmetic subgroups of algebraic groups*, Ann. of Math. 75 (1962), and in R. Godement, *Domaines fondamentaux des groupes arithmétiques*, Séminaire Bourbaki, exposé 257 (1962/63). The finiteness of class numbers is in A. Borel, *Some finiteness properties of adele groups over number fields*, Publ. Math. IHÉS 16 (1963), §§4.5 to 5.8. Platonov and Rapinchuk, *Algebraic Groups and Number Theory*, Chapters 4 and 8, treat both. Mahler's compactness theorem is Chapter V of J. W. S. Cassels, *An Introduction to the Geometry of Numbers*. Weil's convergence criterion is in A. Weil, *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965). The sharp transference bounds are in W. Banaszczyk, Math. Ann. 296 (1993), and earlier bounds in J. C. Lagarias, H. W. Lenstra and C. P. Schnorr, Combinatorica 10 (1990). The model case of $\mathrm{SL}_2(\mathbb{Z})$ is in Serre, *A Course in Arithmetic*, Chapter VII.

The source replaces fundamental domains by cutoffs, Siegel sets by reduced bases with a dyadic profile, and the Witt index condition of Weil by the condition $2t < n$. The finite volume is proved only for unitary groups of hermitian spaces with an adelic orthonormal frame, Mahler's criterion only in one direction, and the finiteness of classes only for the signs $1$ and levels in $K_0$.

Two points in the notes of the plan differ from the source. Finding F-086 lists the finite volume hypothesis of the theorem on right invariance as unused, but the proof uses it, and the theorem is false without it (Section 2). The reference list of the plan gives paths for this chapter, such as `Lib/Adelic/Reduction/Defs` and `Lib/Adelic/QuotientMeasure/Unimodular`, that are not files of the pinned source. The notes also call $J$ a hermitian matrix. The source does not assume this. It follows from $x^* J x = \varepsilon_s$.

Status: drafted by a model. No person has checked this chapter against the Lean source.
