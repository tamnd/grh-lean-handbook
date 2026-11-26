---
title: Siegel's lemma and the gauges of a term
lean:
  - New/Spanning/RemainingTerms/SiegelLemma.lean
  - New/Spanning/RemainingTerms/Discriminants.lean
  - New/Spanning/RemainingTerms/BorderedDeterminant.lean
  - New/Spanning/RemainingTerms/Data.lean
decls:
  - New.Filling.sublatticeDiscriminant
  - New.Filling.siegel_lemma
  - New.Filling.exists_inv_sublatticeDiscriminant_pow_le_prod
  - New.Filling.tsum_sublatticeDiscriminant_inv_le
  - New.Filling.IsLatticeOfRank
  - New.Filling.discriminant
  - New.Filling.submoduleZeta
  - New.Filling.submoduleZeta_prod_le
  - New.Filling.submoduleZeta_pi_le
  - New.Filling.IsLatticeOfRank.tsum_submoduleIndex_inv_pow_le
  - New.Filling.minorNorm
  - New.Filling.subframeMinor
  - New.Filling.HasCellRank.abs_norm_subframeMinor
  - New.Filling.HasCellRank.subframeMinor_ne_zero
  - New.Filling.minorGauge
  - New.Filling.maxGauge
  - New.Filling.HasCellRank.maxGauge_eq
  - New.Filling.latticeDisc
  - New.Filling.one_le_latticeDisc
  - New.Filling.termLattice
  - New.Filling.pairLattice
  - New.Filling.linkCorank
  - New.Filling.levelGauge
  - New.Filling.termSize
  - New.Filling.IsNearRepresentative
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Siegel's lemma and the gauges of a term

The count of the remaining terms sums over subspaces of $X_0$ and over sublattices of a lattice. This section proves that both sums converge, with explicit bounds. It then defines the gauges and the lattices of a term.

Let $E$ be a CM field with a primitive $5040$th root of unity, with $f$ infinite places and root discriminant $\mathrm{rd}$. Let $\kappa$ be a finite set with $k$ elements. Write $\hat{\mathcal{O}}$ for the integral finite adeles and $[a]$ for the generalised index of a finite adele $a$ (`genIndex`). At a unit $a$ it is the inverse of the factor by which $a$ scales Haar measure. At a non-unit it is $0$. At a nonzero $a \in E$ it is $|N_{E/\mathbb{Q}}(a)|$.

### The discriminant of a subspace

Let $u$ be a finite adelic unitary matrix on $E^\kappa$ (`Gf E κ`). It gives the lattice $\Lambda_u = E^\kappa \cap u\hat{\mathcal{O}}^\kappa$ (the `baseLattice` of the moved standard space). For $x \in E^\kappa$ write $\|x\|$ for the Euclidean length of the vector of all images $\Phi_v(x)$, over the $f$ infinite places $v$ together.

**Definition (Discriminant of a subspace).** Let $T \subseteq E^\kappa$ be a subspace of dimension $t$. Let $m$ be the chosen $\kappa \times t$ adelic matrix $m = ya$, with the columns of $y$ a basis of $T$ over $E$, $a$ invertible over $\mathbb{A}_f$ and $u^{-1}m$ primitive. Then $d_u(T) = \sqrt{[\det(m^*m)]}$.

Lean: `New.Filling.sublatticeDiscriminant` (New/Spanning/RemainingTerms/SiegelLemma.lean).

The columns of $m$ form an $\hat{\mathcal{O}}$-basis of the adelic points of $T$ in $u\hat{\mathcal{O}}^\kappa$. So $d_u(T)$ is the discriminant of the lattice $\Lambda_u \cap T$.

**Remark (Formalization).** The basis $m$ is chosen (`sublatticeBasis`, by `Nonempty.some`). Two bases of one lattice give the same value of $[\det(m^*m)]$ (`New.Filling.genIndex_det_gram_eq_of_colLattice_eq`). So $d_u(T)$ does not depend on the choice. The source states the definition for any adelic matrix $H$ with a left inverse. Here $H = u^{-1}$.

### Siegel's lemma

**Lemma (Siegel's lemma).** Let $T \subseteq E^\kappa$ have codimension $s$. Then there are vectors $X_0, \dots, X_{s-1} \in E^\kappa$ with these properties.

1. $T$ is the set of $w$ with $X_i^*w = 0$ for all $i$.
2. Each $X_i$ is a nonzero vector of $\Lambda_u$.
3. $\left(\prod_i \|X_i\|\right)^{2f} \leq (8fs\,\mathrm{rd})^{fs}\, d_u(T)$.

Lean: `New.Filling.siegel_lemma` (New/Spanning/RemainingTerms/SiegelLemma.lean).

*Proof.* Let $m = xb$ be the chosen basis of $\Lambda_u \cap T$, with $x$ over $E$ and $b$ invertible over $\mathbb{A}_f$. Take a matrix $y$ over $E$ whose $s$ columns are a basis of the orthogonal $T^\perp$, so $x^*y = 0$. Take $a$ invertible over $\mathbb{A}_f$ with $u^{-1}ya$ primitive. Jacobi's identity for the complementary primitive matrices $u^{-1}xb$ and $u^{-1}ya$ gives

$$[\det a]^2\,|N_{E/\mathbb{Q}}(\det y^*y)| = [\det(m^*m)] = d_u(T)^2.$$

At each infinite place $v$ choose $r_v \in \mathrm{GL}_s(\mathbb{C})$ such that the columns of $\Phi_v(y)r_v$ are orthonormal. Let $g = (r, a)$ be the adelic matrix with infinite part $r$ and finite part $a$. The product formula gives

$$1 \leq |\det g|\,\sqrt{[\det a]^2\,|N_{E/\mathbb{Q}}(\det y^*y)|} = |\det g|\, d_u(T).$$

Minkowski's second theorem for $g$ ([Chapter](/chapter/reduction-theory/)) gives an invertible $s \times s$ matrix $B$ over $E$ with $a^{-1}B^{\mathsf{T}}$ integral and

$$|\det g| \prod_i \ell(B_i)^{2f} \leq (2fs\,\mathrm{rd})^{fs}.$$

Here $\ell(B_i)$ is the length of the vectors $r_v^{-1}\Phi_v(B_i)$ over all $v$ together. Put $X_i = yB_i$, where $B_i$ is row $i$ of $B$. Then $\|X_i\| = \ell(B_i)$, since $\Phi_v(y)r_v$ has orthonormal columns. The matrix $u^{-1}yB^{\mathsf{T}} = (u^{-1}ya)(a^{-1}B^{\mathsf{T}})$ is integral, so $X_i \in \Lambda_u$. Since $B$ is invertible, the $X_i$ are nonzero and span $T^\perp$, which gives (1) and (2). Multiply the two displayed bounds. This gives $\prod_i \|X_i\|^{2f} \leq (2fs\,\mathrm{rd})^{fs} d_u(T)$, and $2 \leq 8$ gives (3). $\square$

**Lemma (One term of the height zeta function).** Let $T$ have codimension $s$, put $n' = f(k+1)$ and $C = (8fk\,\mathrm{rd})^{n'}$. Then there are vectors $X_i$ with (1) and (2) of Siegel's lemma and

$$\left(d_u(T)^{k+1}\right)^{-1} \leq \prod_{i<s} \left(\|X_i\|^{-2n'}\, C\right).$$

Lean: `New.Filling.exists_inv_sublatticeDiscriminant_pow_le_prod` (New/Spanning/RemainingTerms/SiegelLemma.lean).

*Proof.* Take the $X_i$ of Siegel's lemma and put $P = \prod_i\|X_i\|$. A nonzero vector of $\Lambda_u$ has length at least $1$, so $P \geq 1$. Raise (3) to the power $k + 1$ and use $s \leq k$. This gives $P^{2n'} \leq C^s d_u(T)^{k+1}$. Divide by $P^{2n'} d_u(T)^{k+1}$. If $d_u(T) = 0$, the left side is $0^{-1} = 0$ in the source, and the bound is trivial. $\square$

**Theorem (The height zeta function converges).** For every $s$,

$$\sum_{\operatorname{codim} T = s} \left(d_u(T)^{k+1}\right)^{-1} \leq (200fk\,\mathrm{rd})^{f(k+1)s},$$

the sum over all subspaces $T$ of $E^\kappa$ of codimension $s$, taken in $[0, \infty]$.

Lean: `New.Filling.tsum_sublatticeDiscriminant_inv_le` (New/Spanning/RemainingTerms/SiegelLemma.lean).

*Proof.* For each $T$ take the tuple $(X_0, \dots, X_{s-1})$ of the last lemma. The map from $T$ to its tuple is injective, since $T$ is the orthogonal of the tuple. So the sum is at most the sum over all $s$-tuples of nonzero vectors of $\Lambda_u$ of $\prod_i(C\|X_i\|^{-2n'})$. This sum is $\left(C\sum_{x}\|x\|^{-2n'}\right)^s$, with $x$ over the nonzero vectors of $\Lambda_u$. These vectors have length at least $1$, and two distinct ones differ by a nonzero lattice vector, so they are $1$-separated. The real dimension is $2fk$, and $2n' \geq 2fk + 2$. The packing bound gives $\sum_x \|x\|^{-2n'} \leq 5^{2n'}$. So the sum is at most $(5^2 \cdot 8fk\,\mathrm{rd})^{n's}$, and $5^2 \cdot 8 = 200$. $\square$

### Sums over sublattices

**Definition (Submodule zeta function).** For a ring $R$ and an $R$-module $N$, $\zeta_N(s) = \sum_M [N : M]^{-s}$, the sum over the submodules $M$ of finite index, in $[0, \infty]$.

Lean: `New.Filling.submoduleZeta` (New/Spanning/RemainingTerms/Discriminants.lean).

**Lemma (A product of modules).** Suppose that every ideal of finite index of $R$ is principal. Then $\zeta_{R \times N}(s + 1) \leq \zeta_R(s+1)\,\zeta_N(s)$.

Lean: `New.Filling.submoduleZeta_prod_le` (New/Spanning/RemainingTerms/Discriminants.lean).

*Proof.* Let $M \subseteq R \times N$ have finite index. Its first coordinates form an ideal $I$ of finite index, so $I = (g)$. Put $M' = M \cap N$. Then $[R \times N : M] = [R : I]\,[N : M']$. Choose $n$ with $(g, n) \in M$. Then $M$ is spanned by $(g, n)$ and $M'$. So $M$ is determined by $I$, $M'$ and the class of $n$ modulo $M'$. There are $[N : M']$ classes. So the sum over $M$ is at most $\sum_I [R:I]^{-(s+1)} \sum_{M'} [N:M'] \cdot [N:M']^{-(s+1)}$, which is the right side. $\square$

**Lemma (A free module).** If every ideal of finite index of $R$ is principal, then $\zeta_{R^r}(r + \mu) \leq \zeta_R(\mu)^r$.

Lean: `New.Filling.submoduleZeta_pi_le` (New/Spanning/RemainingTerms/Discriminants.lean).

*Proof.* Induction on $r$. For $r = 0$ the only submodule is $0$, and both sides are $1$. For the step write $R^{r+1} = R \times R^r$. The last lemma gives $\zeta_{R^{r+1}}(r + 1 + \mu) \leq \zeta_R(r + 1 + \mu)\,\zeta_{R^r}(r + \mu)$. The function $\zeta_R$ decreases, so the first factor is at most $\zeta_R(\mu)$. The hypothesis of induction bounds the second factor. $\square$

**Definition (Lattice of rank $r$).** An $\hat{\mathcal{O}}$-submodule $L$ of $\mathbb{A}_f^\kappa$ is a lattice of rank $r$ if it is spanned by the columns of $xa$, with $x$ a $\kappa \times r$ matrix over $E$ with a left inverse and $a \in \mathrm{GL}_r(\mathbb{A}_f)$. Its discriminant is $\sqrt{[\det(B^*B)]}$ for a chosen such basis $B = xa$.

Lean: `New.Filling.IsLatticeOfRank`, `New.Filling.discriminant` (New/Spanning/RemainingTerms/Discriminants.lean).

**Remark (Formalization).** The basis is chosen by `Classical.choose`. If $L$ is not a lattice of rank $r$, the discriminant is the junk value $0$. The lemmas that use it assume that $L$ is a lattice of rank $r$.

**Theorem (Sublattices of a lattice).** Let $L$ be a lattice of rank $r$ and let $\mu \in \mathbb{N}$. Then

$$\sum_{M} [L : M]^{-(r + \mu)} \leq \zeta_{\hat{\mathcal{O}}}(\mu)^r,$$

the sum over the submodules $M \subseteq L$ of finite index, where $\zeta_{\hat{\mathcal{O}}}(\mu)$ is the sum of $[\hat{\mathcal{O}} : I]^{-\mu}$ over the ideals $I$ of finite index (`idealZeta`).

Lean: `New.Filling.IsLatticeOfRank.tsum_submoduleIndex_inv_pow_le` (New/Spanning/RemainingTerms/Discriminants.lean).

*Proof.* The lattice $L$ is the image of a linear map from $\hat{\mathcal{O}}^r$. A submodule of finite index of $L$ pulls back to one of $\hat{\mathcal{O}}^r$ with the same index, and distinct ones pull back to distinct ones. So the sum is at most $\zeta_{\hat{\mathcal{O}}^r}(r + \mu)$. Every ideal of finite index of $\hat{\mathcal{O}}$ contains a nonzero integer, so it comes from a finitely generated ideal of $\mathcal{O}_E$. It is principal since $\hat{\mathcal{O}}$ is a Bézout ring. The last lemma completes the proof. $\square$

Hey's formula gives the sum exactly as a product of zeta values. The source does not use it.

### The gauges of a term

Fix admissible data $S$, classes $c, c'$, and a term $\gamma$ with the cell rank $j$. Write $Z = Z(\gamma)$ and $D_j$ for its leading minor of order $j$.

**Definition (Minor norm and subframe minor).** The minor norm is $\nu_j(\gamma) = |N_{E/\mathbb{Q}}(D_j)| / N^{2(j - \varrho)f}$, with natural subtraction, so the divisor is $N^{2f}$ only at $j = \varrho + 1$. The subframe minor $\delta_*(\gamma)$ is the minor of $Z$ on the rows and columns $a < j$ and $a = \varrho$.

Lean: `New.Filling.minorNorm`, `New.Filling.subframeMinor` (New/Spanning/RemainingTerms/BorderedDeterminant.lean).

**Lemma (The subframe minor).** $|N_{E/\mathbb{Q}}(\delta_*(\gamma))| = N^{2f}\nu_j(\gamma)$. In particular $\delta_*(\gamma) \neq 0$.

Lean: `New.Filling.HasCellRank.abs_norm_subframeMinor`, `New.Filling.HasCellRank.subframeMinor_ne_zero` (New/Spanning/RemainingTerms/BorderedDeterminant.lean).

*Proof.* Let $P$ be the matrix with the rows $a < j$ of $Z$ and the rows of the identity for $a \geq j$. Then $\det P = D_j$. Replace the last row of $P$ by the last row of $Z$. The determinant of the result is $\delta_*(\gamma)$, by expansion along the rows of the identity. If $j = \varrho + 1$, then $P = Z$, and the claim is the definition of $\nu_j$. Let $j \leq \varrho$ and put $y = P^{-1}e_\varrho$. Then $Py = e_\varrho$, so $y_\varrho = 1$, and the new determinant is $(Z_\varrho \cdot y)\det P$. The cell rank gives a shared vector $\gamma\mathfrak{f}y = \mathfrak{f}x$ (`New.Filling.HasCellRank.exists_shared_frame_vector`), with $|\Phi_v(x_\varrho)| = 1$ at each place. So $Z_\varrho \cdot y = h(z, \mathfrak{f}x) = -Nx_\varrho$, whose norm has absolute value $N^{2f}$. Since $\nu_j(\gamma) > 0$, the minor is not zero. $\square$

**Definition (Gauges).** Let $\kappa_\gamma = h_c^{-1}\gamma h_{c'}$. Let $i_\gamma$ be the index, in the lattice spanned by the rows $a < \varrho$ of the products of the frame with $\kappa_\gamma\mathfrak{f}$, of the lattice spanned by the rows $a < j$ (`isotropicRowsIndex`). Let $i'_\gamma$ be the same index for $\kappa_\gamma^{-1}$. Then

$$\mathsf{g}^\sharp = \frac{|N_{E/\mathbb{Q}}(\delta_*(\gamma))|}{i_\gamma i'_\gamma N^f}, \qquad \mathsf{g}^{\max} = \max\left(\mathsf{g}^\sharp, \textstyle\prod_v|\mathsf{g}(\gamma)|_v\right), \qquad \mathsf{g}^* = M^{2\min(\varrho, j)f}\,\mathsf{g}^{\max}.$$

Lean: `New.Filling.minorGauge`, `New.Filling.maxGauge`, `New.Filling.levelGauge` (New/Spanning/RemainingTerms/BorderedDeterminant.lean, New/Spanning/RemainingTerms/Data.lean).

**Lemma (The gauge through the leading minor).** $\mathsf{g}^{\max} = \max\left(\prod_v|\mathsf{g}(\gamma)|_v,\, N^f\nu_j(\gamma)\right) / (i_\gamma i'_\gamma)$.

Lean: `New.Filling.HasCellRank.maxGauge_eq` (New/Spanning/RemainingTerms/BorderedDeterminant.lean).

*Proof.* By the last lemma $\mathsf{g}^\sharp = N^f\nu_j(\gamma)/(i_\gamma i'_\gamma)$. If $\mathsf{g}(\gamma) = 0$, both sides are $\mathsf{g}^\sharp$. Otherwise $j = \varrho + 1$ by the uniqueness of the cell rank, and then $i_\gamma = i'_\gamma = 1$. $\square$

The size of a term is $\operatorname{orbitBound}(\operatorname{cellRank}\gamma, \mathsf{g}^{\max})$ (`termSize`), with the orbit bound of [the box section](/chapter/anatomy-of-a-term/#the-box-and-the-size-of-a-near-term). The kept terms are the near terms that are the chosen element of their double coset $\mathsf{U}^0_c\gamma\,\mathsf{U}^0_{c'}$.

Lean: `New.Filling.termSize` (New/Spanning/RemainingTerms/Data.lean). Lean: `New.Filling.IsNearRepresentative` (New/Spanning/RemainingTerms/BorderedDeterminant.lean).

**Remark (Formalization).** The representative is `Quotient.out` of the double coset, a choice. The count keeps one term from each double coset, and the choice only fixes which term stands for it.

### The lattices of a term

Let $\Lambda$ be the lattice of the class $c$. For a subspace $V$ of $X_0$, the number $\operatorname{latticeDisc}_c(V)$ is $d(\Lambda \cap V)$, the discriminant of a subspace above for the coordinates of $\Lambda$.

Lean: `New.Filling.latticeDisc` (New/Spanning/RemainingTerms/BorderedDeterminant.lean).

**Lemma (Lattice discriminants are at least one).** $1 \leq \operatorname{latticeDisc}_c(V)$.

Lean: `New.Filling.one_le_latticeDisc` (New/Spanning/RemainingTerms/Data.lean).

*Proof.* The basis of $\Lambda \cap X_0$ is orthonormal for the unimodular Gram matrix of $\Lambda$. So vectors of $\Lambda \cap X_0$ have integral products, and the Gram determinant $\det(m^*m)$ is integral. It is a unit, since the discriminant is positive. An integral unit has $[\,\cdot\,] \geq 1$. $\square$

The lattice $L_\gamma$ of a term is the set of $v \in \Lambda \cap X_0$ such that some vector of $v + M(\Lambda \cap A)$ is orthogonal to the frame of $\kappa_\gamma$. For two terms, the common lattice $L_{12}$ is the part of $L_\gamma \cap L_{\gamma'}$ in the common link. The corank of two links is $c^+ = k + 1 - \dim(\mathrm{link}\,\gamma \cap \mathrm{link}\,\gamma')$.

Lean: `New.Filling.termLattice`, `New.Filling.pairLattice`, `New.Filling.linkCorank` (New/Spanning/RemainingTerms/Data.lean).

[The chapter on the remaining terms](/chapter/remaining-terms/) uses the two sums of this section to count the near pairs by these lattices.
