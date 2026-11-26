---
title: The integral as a coset sum
lean:
  - New/UpperBound/Seesaw/IntegralAsCosetSum.lean
  - New/UpperBound/Seesaw/Cut.lean
decls:
  - New.Seesaw.coverMultiplicity
  - New.Seesaw.exists_finset_coverMultiplicity_dvd_pow
  - New.Grading.exists_integral_eq_sum_over_cut
  - New.Data.IsStageCut
  - New.Data.exists_isStageCut
  - New.Data.card_le_residueMatrixCount
  - New.Data.cutSum
  - New.Data.cutSum_comp_smul
  - New.Data.isAdmissibleCombination_cutSum
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The integral as a coset sum

After the unfolding, the outer variable of each stage is integrated over the quotient of $U(Y_j)(\mathbb A)$ by the rational points of the Bessel group. This section replaces each such integral by a finite sum over classes modulo the level, with weights. The weights are inverse multiplicities, and the support theorem of Section 6 makes them finite and nonzero where the integrand is not $0$.

### A weighted fundamental domain

**Definition (Cover multiplicity).** Let $S$, $A$, $J$ be subgroups of a group $H$ and let $T$ be a finite set of cosets in $H/J$. The multiplicity of $t \in H/J$ is the number of classes of $r \in S$ modulo $S \cap A$ with $r^{-1} t \in T$, and $0$ if this number is infinite.

Lean: `New.Seesaw.coverMultiplicity`.

**Remark (Formalization).** The count is `Set.ncard`, which is $0$ on an infinite set. So a multiplicity of $0$ can mean either that no translate of $T$ contains $t$ or that infinitely many do. The users always prove that the multiplicity divides a power of $q$, which excludes both.

**Proposition (A cut exists).** Let $J \subseteq A$ be levels of $U(V)(\mathbb A_f)$, let $D$ be compact and contained in a subgroup $B \supseteq A$, and suppose that for each $x \in D$ there is $n$ with $(x u x^{-1})^{q^n} \in A$ for all $u \in J$. Let $W$ be a property of points such that each point with $W$ has a translate by $S$ in $D$. Then there is a finite $T \subseteq H/J$ such that $T$ is stable under $S \cap A$, every point over $T$ lies in $B$, and the multiplicity divides a power of $q$ at the points of $T$ and at the points with $W$.

Lean: `New.Seesaw.exists_finset_coverMultiplicity_dvd_pow`.

*Proof.* Choose a set $C$ of representatives of the $S$-orbits that meet the image of $D$, and let $T$ be its saturation under $S \cap A$. It is finite, as it lies in the image of the compact set $AD$ modulo the open subgroup $J$. At a coset in $C$ the multiplicity is the index of $Z \cap A$ in the stabilizer $Z$ in $S$. The power condition puts the $q^n$-th powers of $Z$ in $A$, so in the finite quotient of $Z$ by the normal core of $Z \cap A$ every element has order dividing $q^n$, and the index divides a power of $q$ (Lean: `New.Seesaw.exists_index_dvd_pow_of_pow_mem`). $\square$

**Theorem (The integral over a cut).** Let $\mathsf{Y}$ be a grading, $A$ a level and $a$ a function on $U(V)(\mathbb A_\infty)$. There is a constant $\kappa$ such that for every level $J$, finite $T \subseteq U(V)(\mathbb A_f)/J$ and functions $f$ and $b$ the following holds. Suppose $f$ is continuous, left invariant and integrable on the quotient by the rational Bessel points, that $T$ is stable under $R_{\mathrm f} \cap A$, that the multiplicity $m$ is nonzero at each point where $f \neq 0$, and that for $t$ with finite part in $T$ the period of $f$ over the Bessel group at $t$ is $[\,\mathrm{std} : J\,]\, a(t_\infty)\, b(t_{\mathrm f})$. Then

$$\int_{R(E)\backslash U(V)(\mathbb A)} f(g)\, dg = \kappa \sum_{t \in T} m(t)^{-1}\, b(t).$$

Lean: `New.Grading.exists_integral_eq_sum_over_cut`.

*Proof.* Take a cutoff $\beta$ for the Bessel group: a measurable weight whose integral over each orbit is $1$. Average $\beta$ over the finite Bessel group to get a weight $\alpha(g_\infty)\psi(g_{\mathrm f})$ with $\psi = m^{-1}$ on $T$ and $0$ off $T$. Its integral over each orbit is $1$ where $m \neq 0$ (Lean: `New.Seesaw.lintegral_indicator_inv_coverMultiplicity`). Unfolding against this weight turns the integral into the weighted integral of the period, which factors. The archimedean part gives $\kappa = \int a\,\alpha$, and the finite part is the sum over $T$. $\square$

**Remark (Formalization).** The constant $\kappa$ is given by an existence statement and may be $0$. It depends only on $\mathsf{Y}$, $A$ and $a$, which is what the users need, and it goes into the constant $c$ of Section 1.

### The cuts of the tower

**Definition (Stage cut).** For $j \leq 2\varrho + 1$, a stage cut is a finite set $T$ of classes modulo $J_j(\vartheta)$ such that $T$ is stable under $R_j \cap \mathrm{std}$, the points over $T$ are integral at the places prime to $q = \mathrm N\vartheta.Q$, the multiplicity divides a power of $q$ on $T$, and the multiplicity is nonzero at each point with a bounded orbit for `New.Data.twistIdele` $\vartheta$ and $j$.

Lean: `New.Data.IsStageCut`, `New.Data.exists_isStageCut`.

The second Lean name says that a stage cut exists. Its proof applies the proposition, with $W$ the bounded orbit property. A point whose lattice lies between $\bar q^{\,j}\Lambda^-$ and $q^{-j}\Lambda^-$ is a translate of one of finitely many cosets of the standard level supported on $\vartheta.Q \cup \overline{\vartheta.Q}$, and the power condition holds for these (Lean: `New.Data.exists_conj_pow_mem_stdLevel`). The set $\Omega_j$ (Lean: `New.Data.cutPoints`) is the image of the chosen level for $j = 0$ and a chosen stage cut for $j > 0$.

**Remark (Formalization).** For $j > 0$, $\Omega_j$ is defined by `choose`. Only the four properties of a stage cut are used.

**Proposition (The size of a cut).** If $\vartheta.Q = \emptyset$ and $k < m$, every finite set $T$ of classes modulo $J_k(\vartheta)$ whose points are integral has at most $M^{f n^2}$ elements, where $M = p_0 p_1$, $f$ is the number of infinite places of $E$ and $n = n(m)$.

Lean: `New.Data.card_le_residueMatrixCount`.

*Proof.* With $\vartheta.Q = \emptyset$, the level is the subgroup of the standard level that reduces to $1$ at the chosen places, which lie above $p_0$ and $p_1$. Distinct classes of integral points give distinct matrices modulo the chosen places, and there are at most $M^{f n^2}$ such residue matrices. $\square$

**Definition (The cut sum).** For a function $S$ on tuples of classes, $\Sigma_k S$ is the sum of $S$ over $\Omega_0 \times \dots \times \Omega_{k-1}$, each term divided by the multiplicities of its coordinates, with the coordinates from $k$ on the class of $1$.

Lean: `New.Data.cutSum`.

**Theorem (Properties of the cut sum).**

1. $\Sigma_k S$ does not change if $S$ is translated by a tuple $h$ with $h_i$ in the image of the level of $U(X_i)$ for $i < k$ and $h_i = 1$ for $i \geq k$.
2. $\Sigma_k S$ is an admissible combination of the values of $S$ at tuples of points integral away from $q$, with coefficients integral away from $q$. If $\vartheta.Q = \emptyset$, the absolute sum of the coefficients under each automorphism of $\mathbb C$ is at most $(M^{f n^2})^k$.

Lean: `New.Data.cutSum_comp_smul`, `New.Data.isAdmissibleCombination_cutSum`.

*Proof.* (1) The image of the level of $U(X_i)$ lies in $R_i \cap \mathrm{std}$, which permutes $\Omega_i$ and preserves the multiplicities (Lean: `New.Data.smul_mem_cutPoints_iff`, `New.Data.cutMultiplicity_smul`). (2) By induction on $k$ with the closure properties of admissible combinations from Section 2. The weights $m^{-1}$ are integral away from $q$, since $m$ divides a power of $q$, and each stage adds at most $M^{f n^2}$ terms of absolute weight at most $1$ by the size proposition. $\square$
