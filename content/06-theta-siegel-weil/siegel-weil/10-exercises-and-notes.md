---
title: Exercises and notes
lean:
  - Lib/SiegelWeil/OneVector/SiegelClassSum.lean
  - Lib/SiegelWeil/NeighbourLattices.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** At an integral place $A$, let $g$ be a unit and $x_0$ a vector in $A^\kappa$. Use the fact that $\{x \in A : g^{-1}x \in R\}$ has volume $|g|$ to show that the class $x_0 + gL$ has volume $|g|^{\#\kappa}$.

*Hint.* $gL$ is a product of such sets, and Haar measure is invariant under translation.

**Exercise 2.** Let $u$ be a vector of finite adeles and $P = u\bar u^{\mathsf T}$. Show that $P^2 = \langle u, u\rangle P$. Deduce that $1 - cP$ is unitary for the standard form if $c + \bar c = \bar c c \langle u, u\rangle$.

*Hint.* Expand $(1 - cP)^{\mathsf H}(1 - cP)$ and use $P^{\mathsf H} = P$.

**Exercise 3.** Let $w$ be a split finite place, so $w \ne \bar w$. Let $s$ be a finite adele supported at $w$ with $s + \bar s$ integral. Show that $s$ is integral. Deduce that $0$ is the only neighbour residue at $w$.

*Hint.* $\bar s$ is supported at $\bar w$.

**Exercise 4.** In the proof of the bound for the finite density at one, the zeta lemma is applied with $u + 1$, $v = u$ and $n = 1$, so that $\mu = 2u + 5$. Check that the rank condition $2(\mu + 1) \le \#n$ of the integral bound is $4u + 12 \le \#n$, and that $[E : \mathbb{Q}] \le 2^u$ follows from $8f \le 2^u$.

*Hint.* A CM field has $[E : \mathbb{Q}] = 2f$.

**Exercise 5.** Let $H \le K \le L$ be subgroups of finite index. Show that $[L : H] = [L : K][K : H]$. Use this to prove the step $q_w |\Delta(\rho\gamma)|^2 \le |\Delta(\gamma)|^2$, given that $K/H$ has at least $q_w$ elements.

*Hint.* The squared absolute values of $\Delta(\gamma)$ and $\Delta(\rho\gamma)$ are $[L : H]$ and $[L : K]$.

## Notes and references

**The Siegel-Weil formula.** The source names A. Weil, *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965), n° 52, Theorem 5, for the formula in the convergent range. Weil treats all classical dual pairs, and the source treats a split hermitian space of rank $2p$ and one of rank above $2p$ over a CM field with Weil data. For the method the source names Andrianov (1979), Harris (1981), and P. Garrett, *The Siegel-Weil formula in the convergent range* (notes, 2005). For the constancy theorem of Section 5 it names G. Shimura, *Arithmetic of unitary groups*, Ann. of Math. 79 (1964). This chapter has not checked these works, nor the works named below.

**Siegel's formula and local densities.** For Siegel's formula the source names C. L. Siegel, Ann. of Math. 36 (1935), and H. Braun, *Zur Theorie der hermitischen Formen*, Abh. Math. Sem. Hamburg 14 (1941). The source bounds the local densities by Gauss sums and an ideal zeta value and does not evaluate them. The semilocal bound is used in [Volume 10](/chapter/finite-densities/).

**Masses.** For the mass formula the source names W. T. Gan, J. Hanke and J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), and M. Kirschmer, *Definite quadratic and hermitian forms with small class number* (2016), 4.2.7 and 4.2.9.

**Neighbours and reproduction.** The source names M. Greenberg and J. Voight (2014), section 5, for neighbours, and S. Böcherer, Math. Z. 183 (1983), and J.-S. Li, J. Reine Angew. Math. 428 (1992), for the basis problem.

**Remarks on the source.** The docstring of `New.SiegelWeil.siegel_weil` speaks of a mean, while the Lean statement equates the integral with the mass times the sum of zero terms. The hypothesis `h_torus` is a hypothesis of `New.Exchange.IsAutFunction.apply_eq_apply_one`, not of `New.SiegelWeil.siegel_weil`. Its only call site discharges it.

Status: drafted by a model. No person has checked this chapter against the Lean source.
