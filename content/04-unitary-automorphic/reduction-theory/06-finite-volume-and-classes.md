---
title: Finite volume and the finiteness of classes
lean:
  - Lib/Adelic/Reduction/FiniteVolume.lean
  - Lib/Adelic/Reduction/DefiniteClassSums.lean
decls:
  - New.Core.exists_isCompact_profileBases
  - New.Space.quotMeasure
  - New.Space.lintegral_encard_ne_top
  - New.Space.isFiniteMeasure_quotMeasure
  - New.exists_isBoundedDualBasis
  - New.Space.mahler_criterion
  - New.Space.isCocompact_of_definite
  - New.Space.isCocompact_Gamma
  - New.Space.isCocompact_finitePart
  - New.Space.hasFiniteType_of_isLevel
  - New.measureReal_eq_inv_stdLevelIndex
  - New.Space.integral_quotMeasure_eq_classSum
  - New.Space.classIntegral_eq_integral
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Finite volume and the finiteness of classes

This section proves the four finiteness results of the chapter. The first is Weil's criterion: a count of rational matrices is integrable over $\Gamma_V \backslash G$. Its special case $t = 0$ is the finite volume of $\Gamma_V \backslash G$. The second is one half of Mahler's criterion. The third is the compactness of the quotient for a definite space. The fourth is the finiteness of classes for the definite space with all signs $1$, together with the formula that turns an integral over the quotient into a finite class sum.

### The classical statements

Let $\mathbf{G}$ be a reductive group over a number field $F$. By Borel and Harish-Chandra, and in the adelic form of Godement and Borel (Borel, Publ. Math. IHÉS 16 (1963), §§4.5 to 5.8), the quotient $\mathbf{G}(F) \backslash \mathbf{G}(\mathbb{A}_F)^1$ has finite volume. It is compact if and only if $\mathbf{G}$ is anisotropic over $F$. For an open compact subgroup $K$ of $\mathbf{G}(\mathbb{A}_{F,f})$, the set $\mathbf{G}(F) \backslash \mathbf{G}(\mathbb{A}_{F,f}) / K$ is finite. Platonov and Rapinchuk give these results in Chapters 4 and 8 of *Algebraic Groups and Number Theory*.

Weil studied the convergence of theta integrals (A. Weil, *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965)). For a Schwartz function $\phi$ on $V^t$, the theta function $\theta_\phi(g) = \sum_{\xi \in V(F)^t} \phi(g^{-1} \xi)$ has an absolutely convergent integral over the quotient under a condition on the dimension of $V$, the number $t$ and the Witt index of $V$. The source cites Proposition 8 of that paper. A theta function is bounded by a constant times a count of rational points in a compact set, so the integrability of such counts is the main step.

### Reduced bases with a profile

The proofs of the source do not use Siegel sets. They use reduced bases of the adelic lattices, with a coarse coordinate.

For $x \in \mathbb{Z}^n$, let $D(x)$ be the diagonal adelic matrix with entries $2^{x_i}$ at every infinite place and $1$ at the finite places. Let $M$ be a set of invertible adelic matrices. For $y \in \mathrm{GL}_n(\mathbb{A}_E)$, a rational basis $Y \in \mathrm{GL}_n(E)$ has *profile* $x$ for $M$ at $y$ if $y^{-1} Y D(x)^{-1} \in M$. In words, the column $j$ of $Y$ has length about $2^{x_j}$ in the coordinates of $y$.

**Theorem (Reduction theory with profiles).** There are a compact set $M$ of invertible adelic matrices and an integer $c$ with the following property. Every $y \in \mathrm{GL}_n(\mathbb{A}_E)$ has a profile $x \in \mathbb{Z}^n$ and a rational basis $Y$ of profile $x$ for $M$ at $y$. If $|\det y| \ge 1$ for the idele modulus, then $\sum_i x_i \le c$.

Lean: `New.Core.exists_isCompact_profileBases` (Lib/Adelic/Reduction/FiniteVolume.lean).

*Proof.* Take the reduced basis of [Section 4](/chapter/reduction-theory/#minkowskis-theorems-over-e): columns $Y_j$ with $y^{-1} Y_j$ integral at the finite places, lengths at most $2^{x_j}$, and $|\det y| \cdot 4^{f \sum x_i} \le C$ with $C = \max\big((8fn \cdot \mathrm{rd})^{fn}, 1\big)$. Then $y^{-1} Y D(x)^{-1}$ has entries of absolute value at most $1$ at the infinite places and integral entries at the finite places. Its determinant has modulus at least $C^{-1}$, by the product formula for $\det Y$. The set of matrices with these two properties is compact. The bound $\sum x_i \le c$ follows from $4^{f \sum x_i} \le C$ when $|\det y| \ge 1$. $\square$

A point of $\mathbb{Z}^n$ plays the part of a point of $A_t$ in a Siegel set.

### Weil's criterion

The quotient measure of a space is the measure of [Section 2](/chapter/reduction-theory/#integration-on-a-quotient-by-a-cutoff) for the Haar measure of $G$ and the counting measure on $\Gamma_V$.

Lean: `New.Space.quotMeasure` (Lib/Adelic/Reduction/FiniteVolume.lean).

For $g \in G$, write $\tilde g = x g x^{-1}$. This is the matrix of $g$ in the rational coordinates of $V$, and it lies in the adelic unitary group of $J$.

**Theorem (Weil's criterion).** Let $V$ be a space with any signs, let $t$ be a finite set, and let $\Omega$ be a compact set of adelic $n \times t$ matrices. Assume that $2|t| < n$ if $n \ge 1$. Then
$$\int_{\Gamma_V \backslash G} \#\{\xi \in M_{n \times t}(E) : \tilde g^{-1} \xi \in \Omega\} \, dg < \infty.$$

Lean: `New.Space.lintegral_encard_ne_top` (Lib/Adelic/Reduction/FiniteVolume.lean).

*Proof.* The idea is to compare two counts at each $g$. The number of rational matrices $\xi$ is large when the lattice at $g$ has short vectors. The number of reduced bases at $g$ is large in the same situation. The second count unfolds to a finite integral.

Fix $M$ and $c$ from the theorem on profiles. Let $g \in G$ and let $Y$ be a basis of profile $x$ at the moved point $xg$. The modulus of $\det(xg)$ is $1$, so $\sum x_i \le c$.

*Step 1: the count of $\xi$.* The rows of $Y^{-1}\xi$ are $2^{-x_i}$ times rows of vectors in a fixed compact set. By the count of rational points in dyadic boxes (Section 4), there is a constant $C_1$, independent of $g$, $x$ and $Y$, such that the count at $g$ is at most $C_1 \nu(x)$ with
$$\nu(x) = 4^{f |t| \sum_i (-x_i)_+}.$$

*Step 2: many bases.* If $Y$ has profile $x$, then so has $Y(1 + u)$, after $M$ is replaced by $M \cdot B$ with $B$ a fixed compact box. Here $u$ is any matrix of integers of $E$ with $u_{ij} = 0$ unless $x_i < x_j$, and with $u_{ij}$ of size less than $2^{x_j - x_i}$ at the infinite places. Minkowski's first theorem counts these $u$. With $R = ((2\,\mathrm{rd})^f)^{n^2}$ and $T(x) = \sum_{i,j} (x_i - x_j)_+$, the number of bases of profile $x$ for $M B$ at $xg$ is at least $4^{f T(x)}/R$.

*Step 3: the Gram matrices.* Two bases $Y, Y'$ at points of $G$ with the same Gram matrix $Y^* J Y = Y'^* J Y'$ differ by an element $\gamma = Y' Y^{-1}$ of the rational unitary group. The entries $(Y^* J Y)_{ij}$, divided by $2^{x_i + x_j}$ at the infinite places, lie in a fixed compact set. The entries are rational hermitian matrices, so the number of Gram matrices of profile $x$ is at most a constant times $P(x) = 2^{f \sum_{i,j} (x_i + x_j)_+}$. So the number of bases of profile $x$ at $xg$ is at most a sum, over the Gram values $T$ and over $\gamma \in \Gamma_V$, of the indicator functions of $\gamma g \in A_T B'$, for points $A_T$ and one compact set $B'$. Unfold the sum over $\Gamma_V$ by Section 2. This gives the following. Let $\omega(x) \ge 0$ be weights with
$$\sum_{x \in \mathbb{Z}^n} P(x)\, \omega(x) < \infty,$$
and let $h \ge 0$ be a function on $G$ such that each $g$ has a profile $x$ with $h(g) \le \omega(x)$ times the number of bases of profile $x$ at $xg$. Then $h$ has a finite integral over the quotient.

*Step 4: the exponents.* The profile of a reduced basis at a point $xg$ is nearly symmetric: for some permutation $\sigma$ of the indices, $|x_{\sigma(i)} + x_i| \le B$, where $B$ depends only on $M$, $c$ and the signs. The reason is that the Gram matrix is invertible, its entry $(i, j)$ is bounded by a constant times $2^{x_i + x_j}$, and its nonzero entries cannot be too small, by Section 4. Let $q > 1$ with $q^2 = 2^f$. An elementary inequality between the exponents, which uses $2|t| < n$ and the near symmetry, gives
$$C_1 \nu(x) P(x) q^{\sum_i |x_i|} \le C_2 \, 4^{f T(x)}$$
for a constant $C_2$. Put $\omega(x) = C_2 R \prod_i q^{-|x_i|} / P(x)$. Steps 1 and 2 give count at $g \le \omega(x) \cdot \#\{\text{bases of profile } x\}$. The sum of $P(x)\omega(x) = C_2 R \prod_i q^{-|x_i|}$ over $x \in \mathbb{Z}^n$ is a product of $n$ convergent geometric series. Step 3 ends the proof. $\square$

**Corollary (Finite volume).** For every space $V$, with any signs, the quotient measure of $V$ is finite.

Lean: `New.Space.isFiniteMeasure_quotMeasure` (Lib/Adelic/Reduction/FiniteVolume.lean).

*Proof.* Take $t$ empty and $\Omega$ the whole space of $n \times 0$ matrices. There is exactly one such matrix, so the integrand is $1$. $\square$

**Remark (Formalization).** The classical criterion of Weil involves the Witt index. The source proves it only under the condition $2t < n$, which does not depend on $V$. For a definite space the classical result has no condition at all, since the quotient is compact and theta functions are continuous. The argument applies the criterion in the Siegel and Weil formula, where the condition holds. The finite volume is proved only for the quotients $\Gamma_V \backslash G$ of the spaces of [the adeles chapter](/chapter/adeles-hermitian-spaces/#the-spaces-and-groups-of-the-source), that is, for hermitian spaces with an adelic orthonormal frame. It is proved by the counts above and not by a fundamental domain. The constants $C_1$, $C_2$ and $B$ come from existence statements and are not explicit in the statement, which only asserts that the integral is not $\infty$. The integral is the integral of a function with values in $[0, \infty]$, so no integrability hypothesis and no junk value enter.

### Mahler's criterion

**Theorem (Mahler's criterion, one direction).** For every real $R$ there is a compact set $C \subset G$ such that every $g \in G$ with $\operatorname{ht}_V(g) \le R$ has $\gamma g \in C$ for some $\gamma \in \Gamma_V$.

Lean: `New.Space.mahler_criterion` (Lib/Adelic/Reduction/DefiniteClassSums.lean).

*Proof.* Let $N_0$ be the absolute norm of the different. It is a nonzero natural number in the different, so the short basis theorem of [Section 5](/chapter/reduction-theory/#the-first-minimum-and-the-height) applies with $c = 6 N_0 (fn)^2$. At a point $g$ with $\operatorname{ht}_V(g) \le R$ there is a rational basis $Y$ whose columns lie in the lattice of $Vg$ and have length at most $c\,\operatorname{ht}_V(g) \le cR$. So $(xg)^{-1} Y$ lies in the compact box of matrices with entries of absolute value at most $cR$ at the infinite places and integral entries at the finite places. The Gram matrix $Y^* J Y$ is a rational matrix in a compact set, so it takes finitely many values $T_1, \dots, T_k$ as $g$ varies. Fix one basis $Y_j$ of each value. If $Y$ has the value $T_j$, then $\gamma = Y_j Y^{-1}$ preserves $J$, so it is a rational point, and $(\gamma g)^{-1}$ lies in a compact set built from the box and the finitely many $Y_j$. $\square$

**Remark (Formalization).** The theorem states only this direction. The converse, that the points of a compact set have bounded height, is not part of it. The constant $c$ is chosen once, by the norm of the different, and the representatives $Y_j$ are chosen by an inverse function. The compact set $C$ depends on these choices.

**Proposition (Mahler's criterion for frames of varying forms).** Let $K$ be a compact set of invertible adelic matrices. There are a finite set $F$ of rational matrices and compact sets $C$ and $C_f$ with the following property. For every invertible rational $J$ and every adelic $y$ with $y^* J y \in K$, there are a rational basis $Y$ and a set $s$ of its columns such that the columns in $s$ span a totally isotropic subspace for $J$, the basis $W$ dual to $Y$ for $J$ satisfies $W^{-1} y \in C_f$ at the finite places, and the matrix $Z$ made from $W$ by setting the columns in $s$ to $0$ has $y^{-1} Z \in C$ and $Z^* J Z \in F$.

Lean: `New.exists_isBoundedDualBasis` (Lib/Adelic/Reduction/FiniteVolume.lean).

The idea is the same: take a reduced basis, call a column short when its profile entry is below a fixed bound, and note that the form vanishes on pairs of short columns, by the vanishing lemma of Section 4. This version is used for the trace formula and for the range of the Siegel and Weil formula. It is not used by name in the argument.

### Compactness for definite spaces

**Theorem (Compactness).** If all signs of $V$ are equal, there is a compact set $C \subset G$ that meets every coset $\Gamma_V g$. In particular this holds for every space with all signs $1$. For such a space, the group $\Gamma_{V,f}$ is also cocompact in $G_f$.

Lean: `New.Space.isCocompact_of_definite`, `New.Space.isCocompact_Gamma`, `New.Space.isCocompact_finitePart` (Lib/Adelic/Reduction/DefiniteClassSums.lean).

*Proof.* By Section 5 all heights of a definite space are $1$. Apply Mahler's criterion with $R = 1$. For the finite part, project the compact set to $G_f$. $\square$

This is the anisotropic case of the theorem of Borel and Harish-Chandra and of Mostow and Tamagawa. The source proves it by the short vectors argument of Section 5: a definite form has no short lattice vectors, so the lattices cannot degenerate.

### Finiteness of classes

A *level* is an open subgroup $K$ of $K_0$. Its index $[K_0 : K]$ is finite since $K_0$ is compact. Since $\operatorname{vol}(K_0) = 1$, $\operatorname{vol}(K) = [K_0 : K]^{-1}$.

Lean: `New.measureReal_eq_inv_stdLevelIndex` (Lib/Adelic/Reduction/DefiniteClassSums.lean).

**Theorem (Finiteness of classes).** Let $V$ be a space with all signs $1$ and let $K$ be a level. Then the double coset space $\Gamma_{V,f} \backslash G_f / K$ is finite, and for every $g \in G_f$ the group $\Gamma_{V,f} \cap g K g^{-1}$ is finite.

Lean: `New.Space.hasFiniteType_of_isLevel` (Lib/Adelic/Reduction/DefiniteClassSums.lean).

*Proof.* Let $C \subset G_f$ be a compact set that meets every coset $\Gamma_{V,f} g$. The open cosets $hK$ cover $C$, so finitely many of them do. Every double coset $\Gamma_{V,f} g K$ contains a point $\gamma g \in C$, so it is one of the double cosets of these finitely many $hK$. The group $\Gamma_{V,f}$ is discrete and closed in $G_f$, and $g K g^{-1}$ is compact, so their intersection is finite. $\square$

For $f$ a function on $G_f$, left invariant under $\Gamma_{V,f}$ and right invariant under $K$, the *class sum* is
$$\sum_{c \in \Gamma_{V,f} \backslash G_f / K} \frac{f(g_c)}{\#(\Gamma_{V,f} \cap g_c K g_c^{-1})},$$
with $g_c$ a representative of $c$.

**Theorem (Integrals over a definite quotient are class sums).** Let $V$ be a space with all signs $1$. Let $F$ be a continuous function on $G$, left invariant under $\Gamma_V$. Let $f(h) = \int_{G_\infty} F(u, h)\, du$, and let $K$ be a level with $f(hk) = f(h)$ for all $h \in G_f$ and $k \in K$. Then
$$\int_{\Gamma_V \backslash G} F \, dg = [K_0 : K]^{-1} \sum_{c \in \Gamma_{V,f} \backslash G_f / K} \frac{f(g_c)}{\#(\Gamma_{V,f} \cap g_c K g_c^{-1})}.$$
For a function $y$ on $G_f$ that is left invariant under $\Gamma_{V,f}$ and has an open stabilizer on the right, the class integral of $y$ at level $K$ is $[K_0 : K]$ times the integral of $g \mapsto y(g_f)$ over $\Gamma_V \backslash G$.

Lean: `New.Space.integral_quotMeasure_eq_classSum`, `New.Space.classIntegral_eq_integral` (Lib/Adelic/Reduction/DefiniteClassSums.lean).

*Proof.* Cut $G$ into the sets $G_\infty \times \Gamma_{V,f} g_c K$. The projection to $G_f$ maps $\Gamma_V$ bijectively onto $\Gamma_{V,f}$. On one piece, unfold the sum over $\Gamma_V$ as in Section 3. The elements $\gamma$ with $\gamma g_c K = g_c K$ are the stabilizer $\Gamma_{V,f} \cap g_c K g_c^{-1}$, so the unfolding counts each point of the piece as many times as the stabilizer has elements. This gives the weight. The integral of $F$ over $G_\infty \times g_c K$ is $\operatorname{vol}(K) f(g_c) = [K_0:K]^{-1} f(g_c)$, since $f$ is constant on $g_c K$. For the class integral, apply the first statement at the level $K' = K \cap \operatorname{Stab}(y)$ and use $[K_0 : K'] = [K : K'][K_0 : K]$. $\square$

**Example.** Take $n = 1$, so $V = I_1$. Then $G_\infty = (S^1)^f$, $G_f$ is the group of finite ideles of $E$ of norm $1$ to $F$, $K_0$ is its subgroup of units, and $\Gamma_{V,f}$ is the group $E^1$ of elements of $E$ of norm $1$. The groups are commutative, so $\Gamma_{V,f} \cap g K_0 g^{-1} = E^1 \cap K_0$. Its elements are elements of $E$ that are units at every finite place and have absolute value $1$ at every infinite place. By Kronecker's theorem these are the roots of unity $\mu_E$ in $E$. With $F = 1$, the theorem gives
$$\operatorname{vol}(\Gamma_V \backslash G) = \frac{h_1}{\#\mu_E}, \qquad h_1 = \#\big(E^1 \backslash \mathbb{A}_{E,f}^1 / \hat{\mathcal{O}}_E^1\big),$$
in the normalization $\operatorname{vol}(G_\infty) = \operatorname{vol}(K_0) = 1$ of the source.

**Remark (Formalization).** The finiteness of classes is proved only for spaces with all signs $1$ and levels inside $K_0$. This is the case of the forms on definite unitary groups that the argument uses. The index $[K_0 : K]$ is a natural number with the junk value $0$ when the index is infinite. For a level it is finite and nonzero, so the factor $[K_0 : K]^{-1}$ is the true inverse. The class sum is a finite sum with weights $1/\#(\cdots)$, where a cardinality has the junk value $0$ for an infinite set. The theorem on finiteness of classes excludes this. The class sum is `New.classSum` (Lib/Adelic/Hecke/Basic.lean). Its representatives $g_c$ are chosen, but the class sum of an invariant function does not depend on the choice. The Haar measures of $G_f$ and $G$ are right invariant, because the rational points of the standard space are a lattice in $G_f$ (Section 2).

### Where the argument uses this section

Weil's criterion makes the theta integrals of the Siegel and Weil formula converge. Mahler's criterion gives the convergence of theta lifts and the cusp forms of [automorphic forms](/chapter/automorphic-forms/). The compactness of the definite quotient makes continuous functions integrable in the seesaw stages of [Theorem A: the plan](/chapter/theorem-a-plan/) and in the periods of the false lifts of [Theorem C: the plan](/chapter/theorem-c-plan/). The class sum formula turns the periods of false lifts, the norm of the character lift and the explicit matching of the exchange step into finite sums.

**Remark (Formalization).** `New.Space.lintegral_encard_ne_top` is used in Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean. `New.Space.mahler_criterion` is used in Lib/Weil/DualPair/ThetaLiftConvergence.lean and Lib/Adelic/AutomorphicForms/Cuspidality.lean. `New.Space.isCocompact_Gamma` is used in New/UpperBound/Seesaw/UnfoldingStages.lean, and `New.Space.isCocompact_of_definite` in New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean. `New.Space.integral_quotMeasure_eq_classSum` is used in New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean, New/OneLift/HeckeValues/CharacterLiftNorm.lean and New/Determinant/Exchange/ExplicitMatching.lean. `New.Space.classIntegral_eq_integral` is used in Lib/SiegelWeil/OneVector/SiegelClassSum.lean.
