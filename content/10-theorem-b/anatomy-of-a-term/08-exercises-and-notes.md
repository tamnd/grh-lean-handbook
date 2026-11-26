---
title: Exercises and notes
lean:
  - New/Spanning/RemainingTerms/SiegelLemma.lean
  - New/Spanning/RemainingTerms/Discriminants.lean
  - New/Spanning/RemainingTerms/BorderedDeterminant.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $T$ be a hyperplane of $E^\kappa$. Show that $T$ is the orthogonal of one nonzero vector $X \in \Lambda_u$ with $\|X\|^{2f} \leq (8f\,\mathrm{rd})^f d_u(T)$. Then show that $d_u(T) \geq (8f\,\mathrm{rd})^{-f}$.

*Hint.* Put $s = 1$ in [Siegel's lemma](/decl/New.Filling.siegel_lemma/). For the second claim use that a nonzero vector of $\Lambda_u$ has length at least $1$.

**Exercise 2.** Let $H \geq 1$. Show that the number of subspaces $T$ of codimension $s$ with $d_u(T) \leq H$ is at most $H^{k+1}(200fk\,\mathrm{rd})^{f(k+1)s}$.

*Hint.* Each such $T$ contributes at least $H^{-(k+1)}$ to the sum of [the theorem on the height zeta function](/decl/New.Filling.tsum_sublatticeDiscriminant_inv_le/).

**Exercise 3.** Take $R = \mathbb{Z}$. Show that $\zeta_{\mathbb{Z}}(\mu)$ is the Riemann zeta value $\zeta(\mu)$ for $\mu \geq 2$ and is infinite for $\mu \leq 1$. Show that the bound $\zeta_{\mathbb{Z}^r}(r + \mu) \leq \zeta(\mu)^r$ is strict for $r = 1$. For $r = 2$, compare the bound with the exact value $\zeta(2 + \mu)\zeta(1 + \mu)$.

*Hint.* The ideals of finite index of $\mathbb{Z}$ are the $n\mathbb{Z}$ with $n \geq 1$. For $r = 2$ follow the proof of [the lemma on a product of modules](/decl/New.Filling.submoduleZeta_prod_le/). Each submodule of index $n$ is counted once, and the sum over the classes modulo $M'$ is exact.

**Exercise 4.** Let $\gamma$ have the top cell rank $\varrho + 1$. Show that $\delta_*(\gamma) = D_{\varrho+1}$ and that $\mathsf{g}^{\max} = \max\left(\prod_v|\mathsf{g}(\gamma)|_v,\ |N_{E/\mathbb{Q}}(D_{\varrho+1})|/N^f\right)$.

*Hint.* At $j = \varrho + 1$ every index $a$ satisfies $a < j$. Use [the gauge through the leading minor](/decl/New.Filling.HasCellRank.maxGauge_eq/) and the definition of the minor norm.

**Exercise 5.** Let $\gamma$ have a cell rank $j \leq \varrho$. Show that $\mathsf{g}^{\max} = \mathsf{g}^\sharp$ and that the numerator $|N_{E/\mathbb{Q}}(\delta_*(\gamma))|$ of $\mathsf{g}^\sharp$ is positive.

*Hint.* Below the top rank the discriminant $\mathsf{g}(\gamma)$ is $0$. Then use [the lemma on the subframe minor](/decl/New.Filling.HasCellRank.subframeMinor_ne_zero/).

**Exercise 6.** Let $L$ be a lattice of rank $r$ and let $\mu \geq 2$. Show that the number of sublattices $M \subseteq L$ of index at most $X$ is at most $X^{r+\mu}\zeta_{\hat{\mathcal{O}}}(\mu)^r$.

*Hint.* Use [the theorem on sublattices of a lattice](/decl/New.Filling.IsLatticeOfRank.tsum_submoduleIndex_inv_pow_le/) as in Exercise 2.

**Exercise 7.** Show that $Z(\gamma^{-1}) = Z(\gamma)^*$. Deduce that the leading minors of $Z(\gamma^{-1})$ are the conjugates of those of $Z(\gamma)$, and that $\nu_j(\gamma^{-1}) = \nu_j(\gamma)$ for every $j$. Then show that the subframe minor of $\gamma^{-1}$ is the conjugate of the subframe minor of $\gamma$.

*Hint.* Since $\gamma$ is unitary, $h(\mathfrak{f}_a, \gamma^{-1}\mathfrak{f}_b) = h(\gamma\mathfrak{f}_a, \mathfrak{f}_b) = \overline{h(\mathfrak{f}_b, \gamma\mathfrak{f}_a)}$. The submatrix of $Z^*$ on a set of rows and the same set of columns is the conjugate transpose of that of $Z$. So a leading minor of $Z^*$ is the conjugate of the leading minor of $Z$, and the norm to $\mathbb{Q}$ is the product of the squared absolute values at the infinite places. The source proves the second claim as `New.Filling.minorNorm_inv`.

## Notes and references

Siegel's lemma goes back to C. L. Siegel, Über einige Anwendungen diophantischer Approximationen, Abh. Preuss. Akad. Wiss. (1929). The form over a number field with the root discriminant is due to E. Bombieri and J. Vaaler, On Siegel's lemma, Invent. Math. 73 (1983). The form in this chapter bounds the product of the lengths by the discriminant of the subspace. The source proves the version here from its own Minkowski theorem, in [the chapter on reduction theory](/chapter/reduction-theory/). An account of Siegel's lemma over $\mathbb{Q}$ is in W. M. Schmidt, Diophantine Approximation, Lecture Notes in Math. 785, Springer (1980).

The sum of $[L : M]^{-s}$ over the sublattices of a lattice is a zeta function of the lattice. Hey's formula expresses it as a product of shifted Dedekind zeta values. The source proves only the upper bound, by induction on the rank, and needs only that the ideals of finite index are principal. Over $\hat{\mathcal{O}}$ this holds because each such ideal contains a nonzero integer and $\hat{\mathcal{O}}$ is a Bézout ring. The bound is weaker than the exact value, but it has the same form: a power of one zeta value.

The height zeta function of the subspaces is the sum of a negative power of the discriminant over the subspaces of a fixed dimension. The source bounds it by the packing bound for the lattice $\Lambda_u$, with Siegel's lemma as the bridge from subspaces to tuples of lattice vectors.

A term of cell rank $j$ has $\operatorname{rk} A/(A \cap \gamma A) = \min(\varrho, j)$. So the cell rank measures the relative position of $A$ and $\gamma A$, as in the Bruhat decomposition. The big cell is the top cell rank $\varrho + 1$. The background is in [the chapter on Bessel subgroups and the big cell](/chapter/bessel-bruhat/).

Status: drafted by a model. No person has checked this chapter against the Lean source.
