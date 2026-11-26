---
title: Exercises and notes
lean:
  - Lib/SiegelWeil/OneVector/SemilocalDensityBounds.lean
  - Lib/SiegelWeil/OneVector/SiegelClassSum.lean
  - Lib/SiegelWeil/NeighbourLattices.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of Sections 2 to 9.

**Exercise 1.** At an integral place $A$, let $g$ be a unit and $x_0$ a vector in $A^\kappa$. Use the fact that $\{x \in A : g^{-1}x \in R\}$ has volume $|g|$ to show that the class $x_0 + gL$ has volume $|g|^{\#\kappa}$.

*Hint.* The lattice $gL$ is a product of one such set for each coordinate. Haar measure is invariant under translation by $x_0$.

**Exercise 2.** Let the hypotheses of the theorem on the mass of the lattice hold, and let $\zeta_R(\mu) \le 1 + \varepsilon$ with $0 \le \varepsilon \le 1$. Show that $|l_t(L) - 1| \le \varepsilon$ for every integral skew $t$. Explain why the hypothesis $\zeta_R(\mu) \le 2$ of the theorem holds.

*Hint.* Subtract $1$ from both sides of $1 + \|l_t(L) - 1\| \le \zeta_R(\mu)$.

**Exercise 3.** Let $u$ be a vector of finite adeles with $\langle u, u\rangle = \bar u^{\mathsf T} u$, and let $P = u\bar u^{\mathsf T}$. Show that $P^2 = \langle u, u\rangle P$. Deduce that $1 - cP$ is unitary for the standard form if $c + \bar c = \bar c c \langle u, u\rangle$.

*Hint.* Expand $(1 - cP)^{\mathsf H}(1 - cP)$ and use $P^{\mathsf H} = P$.

**Exercise 4.** Let $w$ be a split finite place, so $w \ne \bar w$. Let $s$ be a finite adele supported at $w$ with $s + \bar s$ integral. Show that $s$ is integral. Deduce that $0$ is the only neighbour residue at $w$.

*Hint.* The conjugate $\bar s$ is supported at $\bar w$. So the component of $s + \bar s$ at $w$ is the component of $s$.

**Exercise 5.** In the proof of the bound for the finite density at one, the zeta lemma is applied with $u + 1$, $v = u$ and $n = 1$, so that $\mu = 2u + 5$. Check that the rank condition $2(\mu + 1) \le \#n$ of the integral bound is the hypothesis $4u + 12 \le \#n$. Check that the condition $[E : \mathbb{Q}] \le 2^u$ of the zeta lemma follows from $8f \le 2^u$.

*Hint.* A CM field has $[E : \mathbb{Q}] = 2f$.

**Exercise 6.** Start from Siegel's formula for the masses in the form
$$
\mathrm{mass}(j) = \mathrm{mass}(j+1) \cdot |D_E|^{1/4} \Bigl(\frac{\pi^{j+1}}{j!}\Bigr)^f \cdot x \cdot \mathrm{vol}(\widehat{\mathcal O})^{j+1},
$$
with $|D_E| = (\mathrm{rd}_E^f)^2$ and $\mathrm{vol}(\widehat{\mathcal O}) = ((\mathrm{rd}_E/2)^f)^{-1}$. Show that
$$
\log \mathrm{mass}(j+1) - \log \mathrm{mass}(j) - f\Bigl(\bigl(j + \tfrac12\bigr)\log \mathrm{rd}_E + \log j! - (j+1)\log 2\pi\Bigr) = -\log \|x\|.
$$

*Hint.* Take the logarithm of the norm of both sides. The term $(j+1) f \log(\mathrm{rd}_E/2)$ from the volume and the term $\frac f2 \log \mathrm{rd}_E$ from the discriminant combine into $(j + \frac12) f \log \mathrm{rd}_E - (j+1) f \log 2$.

**Exercise 7.** Let $H \le K \le L$ be subgroups of finite index. Show that $[L : H] = [L : K][K : H]$. Use this to prove the step $q_w |\Delta(\rho\gamma)|^2 \le |\Delta(\gamma)|^2$, given that $K/H$ has at least $q_w$ elements.

*Hint.* The squared absolute values of $\Delta(\gamma)$ and $\Delta(\rho\gamma)$ are $[L : H]$ and $[L : K]$.

## Notes and references

**The Siegel-Weil formula.** The source names A. Weil, *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965), n° 52, Theorem 5, for the formula in the convergent range. Weil works with general classical groups and an arbitrary number field. The source pairs a split hermitian space of rank $2p$ with a hermitian space of rank above $2p$, over a CM field with Weil data. For the method of proof the source names Andrianov (1979), Harris (1981), and P. Garrett, *The Siegel-Weil formula in the convergent range* (notes, 2005). This chapter has not checked these works.

**Strong approximation.** The constancy theorem of Section 5 is a weak substitute for strong approximation for special unitary groups. The source names G. Shimura, *Arithmetic of unitary groups*, Ann. of Math. 79 (1964), among its references for this.

**Siegel's formula and local densities.** For Siegel's formula the source names C. L. Siegel, Ann. of Math. 36 (1935), and H. Braun, *Zur Theorie der hermitischen Formen*, Abh. Math. Sem. Hamburg 14 (1941). The source does not evaluate the local densities. It bounds them by Gauss sums and a value of an ideal zeta function. There are two developments of this bound. The adelic one in Lib/SiegelWeil/Mass.lean is used for the ratio of masses. The semilocal one in Lib/SiegelWeil/OneVector is used in [Volume 10](/chapter/finite-densities/).

**Masses.** For the mass formula the source names W. T. Gan, J. Hanke and J.-K. Yu, *On an exact mass formula of Shimura*, Duke Math. J. 107 (2001), and M. Kirschmer, *Definite quadratic and hermitian forms with small class number* (2016), 4.2.7 and 4.2.9. The source proves only an estimate for the ratio of masses in consecutive ranks, with an error $2/2^u$ for $j \ge 4u + 12$.

**Neighbours and reproduction.** For Kneser's neighbours the source names M. Greenberg and J. Voight, *Lattice methods for algebraic modular forms on classical groups* (2014), section 5. For the basis problem in the stable range it names S. Böcherer, *Über die Fourier-Jacobi-Entwicklung Siegelscher Eisensteinreihen*, Math. Z. 183 (1983), and J.-S. Li, J. Reine Angew. Math. 428 (1992).

**Remarks on the source.** Two points in the source text do not match the Lean statements. The docstring of `New.SiegelWeil.siegel_weil` speaks of a mean, while the Lean statement is an equality of the integral with the mass times the sum of zero terms. The hypothesis `h_torus` is a hypothesis of `New.Exchange.IsAutFunction.apply_eq_apply_one`, not of `New.SiegelWeil.siegel_weil`. Its only call site discharges it.

Status: drafted by a model. No person has checked this chapter against the Lean source.
