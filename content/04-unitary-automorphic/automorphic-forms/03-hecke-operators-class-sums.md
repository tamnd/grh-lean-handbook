---
title: Hecke operators and class sums
lean:
  - Lib/Adelic/Hecke/Basic.lean
  - Lib/Adelic/Hecke/ClassSums.lean
decls:
  - New.rightRegular
  - New.levelSpace
  - New.heckeFun
  - New.heckeCoset
  - New.HasFiniteCosets
  - New.IsHeckeFunction
  - New.isHeckeFunction_doubleCoset
  - New.heckeFun_eq_sum
  - New.heckeFun_heckeFun
  - New.IsHeckeFunction.heckeFun_mem
  - New.classAut
  - New.DoubleCosets
  - New.classSum
  - New.card_classAut_mul_mul
  - New.classSum_eq_finsum_of_rep
  - New.rightStabilizer
  - New.classIntegral
  - New.HasFiniteType
  - New.HasFiniteType.of_le
  - New.classIntegral_eq_classSum
  - New.card_classes_eq_classSum
  - New.classSum_pos
  - New.exists_transporter
  - New.classSum_eq_relIndex_smul
  - New.classSum_one_of_le
  - New.IsUnitary
  - New.IsSmoothRep
  - New.compactMean
  - New.compactMean_mem_levelSpace
  - New.compactMean_eq_self
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Hecke operators and class sums

This section gives two finite sums. The first is the Hecke operator of a function on $G/K$: a sum of translates over finitely many cosets. The second is the class sum: a sum over the double cosets $\Gamma \backslash G / K$, each term divided by the order of a stabilizer. On a definite unitary group the class sum is the integral over the quotient, as Section 2 explains. The source defines both sums for an arbitrary group $G$, with no topology and no measure. This makes the definitions short, but it also makes them total: the source assigns a value to every sum, also when the sum has infinitely many nonzero terms. The remarks of this section say where this matters.

Throughout this section, $G$ is a group, $\Gamma$ and $K$ are subgroups of $G$, $A$ is a commutative ring, and $\pi$ is a representation of $G$ on an $A$-module $W$.

### Fixed vectors and Hecke operators

**Definition (Right regular representation).** The *right regular representation* of $G$ on the functions $F : G \to W$ is $(g \cdot F)(x) = F(xg)$.

Lean: `New.rightRegular` (Lib/Adelic/Hecke/Basic.lean).

**Definition (Level space).** For a character $\chi : K \to A^\times$, the *level space* of $(K, \chi)$ is the submodule of the $v \in W$ with $\pi(k)v = \chi(k)v$ for all $k \in K$. For $\chi = 1$ it is the space $W^K$ of $K$-fixed vectors.

Lean: `New.levelSpace` (Lib/Adelic/Hecke/Basic.lean).

In the source the default value of $\chi$ is the trivial character, so `levelSpace π K` is $W^K$. For $G = G_f$, $W$ a space of functions on $G = G_\infty \times G_f$ and $\pi$ right translation, a function lies in $W^K$ if and only if it has level $K$ in the sense of Section 1.

**Definition (Hecke operator).** For $f : G \to A$, the *Hecke operator* of $f$ is $\pi(f) = \sum_{q \in G/K} f(g_q)\pi(g_q)$, where $g_q$ is a chosen representative of the coset $q$. The source sets $\pi(f) = 0$ if infinitely many terms are nonzero. The Hecke operator of the double coset $KgK$ is $\pi(\mathbf{1}_{KgK})$.

Lean: `New.heckeFun`, `New.heckeCoset` (Lib/Adelic/Hecke/Basic.lean).

**Definition (Hecke function).** The function $f$ *has finite cosets* if $f(g_q) \neq 0$ for only finitely many $q \in G/K$. It is a *Hecke function* for $K$ if it has finite cosets and $f(gk) = f(kg) = f(g)$ for all $g \in G$ and $k \in K$.

Lean: `New.HasFiniteCosets`, `New.IsHeckeFunction` (Lib/Adelic/Hecke/Basic.lean).

**Lemma.** Let $G$ be a topological group and $K$ a compact open subgroup. For every $g \in G$ the indicator function of $KgK$ is a Hecke function for $K$.

Lean: `New.isHeckeFunction_doubleCoset` (Lib/Adelic/Hecke/Basic.lean).

*Proof.* The set $KgK$ is compact, as the image of $K \times K$ under $(a, b) \mapsto agb$. It is covered by the open cosets $xK$ with $x \in KgK$, so finitely many of them cover it. The indicator is $K$-invariant on both sides since $KgK$ is. $\square$

**Remark (Formalization).** The representative $g_q$ is the element `q.out` that Lean's quotient gives, a choice made once for each coset by the axiom of choice. The textbook operator is $\int f(g)\pi(g)\,dg$ for the Haar measure with $\operatorname{vol}(K) = 1$. It does not depend on representatives, but it only acts on $K$-fixed vectors. The source's operator is defined on all of $W$. On $W^K$, and for right $K$-invariant $f$, it agrees with the textbook operator, by the next lemma. The argument applies $\pi(f)$ only in this case. The junk value $0$ for a function with infinitely many cosets does not occur in the argument, since each use comes with a proof that $f$ has finite cosets.

**Lemma (Any representatives serve).** Let $f(gk) = f(g)$ for all $g \in G$ and $k \in K$, and let $v \in W^K$. Let $(r_i)_{i \in s}$ be a finite family in $G$ whose cosets $r_i K$ are distinct and cover the support of $f$. Then $f$ has finite cosets, and $\pi(f)v = \sum_{i \in s} f(r_i)\pi(r_i)v$.

Lean: `New.heckeFun_eq_sum` (Lib/Adelic/Hecke/Basic.lean).

*Proof.* If $f(g_q) \neq 0$, then $g_q$ lies in the support of $f$, so $q = r_i K$ for some $i \in s$. So the support of $q \mapsto f(g_q)$ lies in the finite image of $s$, and $f$ has finite cosets. For $g \in G$ the representative of $gK$ is $gk$ for some $k \in K$. Then $f(gk)\pi(gk)v = f(g)\pi(g)\pi(k)v = f(g)\pi(g)v$, because $f$ is right $K$-invariant and $v$ is $K$-fixed. So each term of the sum over $G/K$ is the term at $r_i$ for the unique $i$ with $q = r_iK$, and the terms outside the image of $s$ are $0$. $\square$

**Lemma (Composition).** Let $f$ and $f'$ have finite cosets, let $f$ be right $K$-invariant, and let $v \in W^K$. Let $Q$ be the finite set of cosets $q$ with $f'(g_q) \neq 0$. Then $\pi(f')\pi(f)v = \pi(f' * f)v$, where $(f' * f)(x) = \sum_{q \in Q} f'(g_q)\, f(g_q^{-1}x)$.

Lean: `New.heckeFun_heckeFun` (Lib/Adelic/Hecke/Basic.lean).

*Proof.* By the lemma above, $\pi(g_q)\pi(f)v = \sum_{p} f(g_p)\pi(g_q g_p)v$. The cosets $g_q g_p K$, for $p$ in $G/K$, run once over $G/K$. So by the lemma, applied to the left translate $x \mapsto f(g_q^{-1}x)$, the vector $\pi(g_q)\pi(f)v$ is the operator of that translate applied to $v$. Sum over $q \in Q$ with the weights $f'(g_q)$, and use that $f \mapsto \pi(f)$ is linear on functions with finite cosets. $\square$

The function $f' * f$ is the convolution of $f'$ and $f$ for the Haar measure with $\operatorname{vol}(K) = 1$. So the lemma says that $f \mapsto \pi(f)$ is a homomorphism from the Hecke algebra to the operators on $W^K$.

**Lemma.** Let $f$ be a Hecke function for $K$ and $v \in W^K$. Then $\pi(f)v \in W^K$.

Lean: `New.IsHeckeFunction.heckeFun_mem` (Lib/Adelic/Hecke/Basic.lean).

*Proof.* For $k \in K$ the vector $\pi(k)\pi(f)v$ is, by the proof of the composition lemma with $f'$ the indicator of $kK$, the operator of $x \mapsto f(k^{-1}x)$ applied to $v$. Since $f$ is left $K$-invariant, this function is $f$. $\square$

### Class sums

The class sum is the main tool of the source on a definite group.

**Definition (Stabilizer, double cosets).** For $g \in G$, the group $\Gamma \cap gKg^{-1}$ is the *stabilizer* of $g$, the subgroup of $\Gamma$ that fixes the point $gK$ of $G/K$. The set $\Gamma \backslash G / K$ is the set of double cosets $\Gamma g K$.

Lean: `New.classAut`, `New.DoubleCosets` (Lib/Adelic/Hecke/Basic.lean).

The order of the stabilizer depends only on the double coset: $\#(\Gamma \cap (\gamma g k)K(\gamma g k)^{-1}) = \#(\Gamma \cap gKg^{-1})$ for $\gamma \in \Gamma$ and $k \in K$, since conjugation by $\gamma^{-1}$ carries the first group onto the second.

Lean: `New.card_classAut_mul_mul` (Lib/Adelic/Hecke/Basic.lean).

**Definition (Class sum).** Let $W$ be a $\mathbb{Q}$-vector space and $f : G \to W$. The *class sum* of $f$ is
$$\Sigma_{\Gamma, K}(f) = \sum_{c \in \Gamma \backslash G / K} \frac{f(g_c)}{\#(\Gamma \cap g_c K g_c^{-1})},$$
where $g_c$ is a chosen representative of $c$.

Lean: `New.classSum` (Lib/Adelic/Hecke/Basic.lean).

If $f$ is left $\Gamma$-invariant and right $K$-invariant, the value does not depend on the representatives. Any system of representatives $r$ of $\Gamma \backslash G / K$ gives the same sum.

Lean: `New.classSum_eq_finsum_of_rep` (Lib/Adelic/Hecke/Basic.lean).

**Remark (Formalization).** Two junk values enter the definition. The sum is Lean's `finsum`, which is $0$ when infinitely many terms are nonzero. The order $\#$ is `Nat.card`, which is $0$ for an infinite group, and $0^{-1} = 0$ in $\mathbb{Q}$. So a class with an infinite stabilizer gets weight $0$, and the class sum of a function with infinitely many nonzero terms is $0$. The source states these conventions in the header of the file. On a definite group and a level $K$, there are finitely many classes and all stabilizers are finite. The next definition records these conditions. Every theorem of the source that turns a class sum into an integral, a dimension or a positive number assumes them.

**Definition (Finite type).** The pair $(\Gamma, K)$ *has finite type* if $G$ is a topological group, $K$ is compact and open, $\Gamma \backslash G / K$ is finite, and every stabilizer $\Gamma \cap gKg^{-1}$ is finite.

Lean: `New.HasFiniteType` (Lib/Adelic/Hecke/ClassSums.lean).

For a space $V$ with all signs $+1$ and a level $K$, the pair $(\Gamma_{V,f}, K)$ in $G_f$ has finite type. This is `New.Space.hasFiniteType_of_isLevel` (Lib/Adelic/Reduction/DefiniteClassSums.lean), a special case of the finiteness of class numbers, which [reduction theory](/chapter/reduction-theory/) proves from the compactness of the definite quotient.

**Lemma.** If $(\Gamma, K)$ has finite type and $K' \subseteq K$ is an open subgroup, then $(\Gamma, K')$ has finite type.

Lean: `New.HasFiniteType.of_le` (Lib/Adelic/Hecke/ClassSums.lean).

*Proof.* The open subgroup $K'$ has finite index in the compact group $K$. Each class $\Gamma x K'$ has the form $\Gamma g q K'$ with $g$ a representative of a class for $K$ and $q$ a representative of $K/K'$, so there are finitely many. The stabilizer $\Gamma \cap gK'g^{-1}$ lies in $\Gamma \cap gKg^{-1}$, so it is finite. A closed subset of a compact set is compact, and an open subgroup is closed. $\square$

**Lemma.** Let $(\Gamma, K)$ have finite type, and let all stabilizers be trivial. Then $\Sigma_{\Gamma, K}(1) = \#(\Gamma \backslash G / K)$, as real numbers.

Lean: `New.card_classes_eq_classSum` (Lib/Adelic/Hecke/ClassSums.lean).

**Lemma (Positivity).** Let $(\Gamma, K)$ have finite type, let $W$ be an ordered $\mathbb{Q}$-vector space, and let $f \geq 0$ with $f(g_c) > 0$ for some class $c$. Then $\Sigma_{\Gamma, K}(f) > 0$.

Lean: `New.classSum_pos` (Lib/Adelic/Hecke/ClassSums.lean).

*Proof.* The sum is finite, each weight $1/\#(\Gamma \cap g_c K g_c^{-1})$ is positive because the stabilizer is finite and nonempty, and one term is positive. $\square$

### The class integral

A function on a definite quotient need not be invariant under a given level. The source defines an integral that works at the level of the function.

**Definition (Class integral).** For $f : G \to W$, let $\operatorname{Stab}(f)$ be the subgroup of $k \in G$ with $f(gk) = f(g)$ for all $g$. The *class integral* of $f$ at $(\Gamma, K)$ is
$$I_{\Gamma, K}(f) = [K : K \cap \operatorname{Stab}(f)]^{-1}\, \Sigma_{\Gamma, K \cap \operatorname{Stab}(f)}(f).$$

Lean: `New.rightStabilizer`, `New.classIntegral` (Lib/Adelic/Hecke/ClassSums.lean).

For $(\Gamma, K)$ of finite type and $f$ left $\Gamma$-invariant with open stabilizer, $I_{\Gamma,K}(f)$ is the integral of $f$ over $\Gamma \backslash G$ for the Haar measure with $\operatorname{vol}(K) = 1$. The source uses no measure here. Section 7 proves the match with the measure-theoretic integral on the standard definite space.

**Remark (Formalization).** The index $[K : K \cap \operatorname{Stab}(f)]$ is `Subgroup.relIndex`, which is $0$ when the index is infinite, and then $I_{\Gamma,K}(f) = 0$. This happens when $\operatorname{Stab}(f)$ is not open. The theorems on the class integral assume that the stabilizer is open, so the junk value does not reach the argument.

**Lemma.** If $K \subseteq \operatorname{Stab}(f)$, then $I_{\Gamma,K}(f) = \Sigma_{\Gamma,K}(f)$.

Lean: `New.classIntegral_eq_classSum` (Lib/Adelic/Hecke/ClassSums.lean).

*Proof.* Then $K \cap \operatorname{Stab}(f) = K$ and the index is $1$. $\square$

### Change of level

The main identity on class sums compares two levels. It is the finite form of the statement that a Haar measure with $\operatorname{vol}(K) = 1$ gives the subgroup $L$ volume $[K : L]^{-1}$.

**Lemma (Transporter).** Let $(\Gamma, K)$ have finite type and $g, h \in G$. The set of $\gamma \in \Gamma$ with $g^{-1}\gamma h \in K$ is finite. It has $\#(\Gamma \cap gKg^{-1})$ elements if $\Gamma g K = \Gamma h K$, and it is empty otherwise.

Lean: `New.exists_transporter` (Lib/Adelic/Hecke/ClassSums.lean).

*Proof.* If $\Gamma gK \neq \Gamma hK$, no $\gamma$ satisfies $g^{-1}\gamma h \in K$. If $h = agk$ with $a \in \Gamma$ and $k \in K$, then $g^{-1}\gamma h \in K$ if and only if $\gamma a \in gKg^{-1}$, that is, $\gamma \in (\Gamma \cap gKg^{-1})a^{-1}$. $\square$

The source states the lemma for an injection $u$ into $G$ whose range contains $\Gamma$, so that the same lemma serves for the rational group $U(J)(E)$ and its image in $G_f$.

**Theorem (Change of level).** Let $(\Gamma, K)$ and $(\Gamma, K')$ have finite type. Let $a \in G$, let $L = a^{-1}K'a$, and suppose $L \subseteq K$. Let $f, F : G \to W$ with $f(g_{\Gamma (ga) K}) = F(g)$ for all $g$, where $g_c$ is the chosen representative of the class $c$. Then
$$\Sigma_{\Gamma, K'}(F) = [K : L]\, \Sigma_{\Gamma, K}(f).$$

Lean: `New.classSum_eq_relIndex_smul` (Lib/Adelic/Hecke/ClassSums.lean).

*Proof.* We count the triples $(x, y, \gamma)$, with $x$ and $y$ representatives of classes for $K'$ and $K$ and $\gamma \in \Gamma$, in two ways. For classes $x$, $y$ and a subgroup $U$, let $T_U(y, x)$ be the transporter set of the lemma, the $\gamma \in \Gamma$ with $y^{-1}\gamma x \in U$.

First, fix $x$. The term $F(x)$ is $f$ at the representative of $\Gamma xaK$. By the transporter lemma, $F(x) = \Sigma_{\Gamma,K}\bigl(y \mapsto \#T_K(y, xa)\, f(y)\bigr)$, since the only class $y$ with a nonzero count is the class of $xa$, and there the count cancels the weight.

Second, split each $T_K(y, xa)$ along the cosets of $L$ in $K$. For $\gamma \in T_K(y, xa)$ the element $y^{-1}\gamma xa$ lies in $K$, and it lies in exactly one coset $q_i L$ of $L$ in $K$. The condition $q_i^{-1}y^{-1}\gamma xa \in L$ means $(y q_i a^{-1})^{-1}\gamma x \in K'$. So $\#T_K(y, xa) = \sum_{i} \#T_{K'}(yq_ia^{-1}, x)$, a sum over the $[K:L]$ cosets.

Third, exchange the two finite class sums. For fixed $y$ and $i$, the class sum over $x$ of $\#T_{K'}(yq_ia^{-1}, x) f(y)$ is $f(y)$, by the transporter lemma for $K'$. So
$$\Sigma_{\Gamma,K'}(F) = \Sigma_{\Gamma,K}\Bigl(y \mapsto \sum_{i} f(y)\Bigr) = [K:L]\,\Sigma_{\Gamma,K}(f). \qquad \square$$

**Remark (Formalization).** In the Lean proof the transporter sets come from the lemma by `choose`, one finite set for each subgroup and pair of points. Only their elements and their number enter the proof, so the choice does not affect the statement. The function $F$ is given together with $f$, and the hypothesis ties $F$ to $f$ at the chosen representatives. For $f$ left $\Gamma$-invariant and right $K$-invariant, one can take $F(g) = f(ga)$.

**Corollary.** Let $(\Gamma, K)$ and $(\Gamma, K')$ have finite type with $K' \subseteq K$. Then $\Sigma_{\Gamma,K'}(1) = [K : K']\,\Sigma_{\Gamma,K}(1)$, as real numbers.

Lean: `New.classSum_one_of_le` (Lib/Adelic/Hecke/ClassSums.lean).

*Proof.* Take $a = 1$, $L = K'$, and $f = F = 1$ in the theorem. $\square$

For a definite unitary group, $\Sigma_{\Gamma,K}(1)$ is the *mass* of the level $K$, in the sense of the mass formulas for definite hermitian forms. The corollary says that the mass times $[K_0 : K]^{-1}$ does not depend on $K$.

### Means over a compact group

The class integral also gives the mean over a compact group, with no Haar measure.

**Definition (Unitary form, smooth representation).** Let $\rho$ be a representation of $G$ on a complex vector space $V$. A sesquilinear form $B$ on $V$ is *unitary* for $\rho$ if $B(x, x) > 0$ for $x \neq 0$ and $B(\rho(g)x, \rho(g)y) = B(x, y)$ for all $g$, $x$ and $y$. The representation is *smooth* if every vector is fixed by all $g$ in some neighborhood of $1$.

Lean: `New.IsUnitary`, `New.IsSmoothRep` (Lib/Adelic/Hecke/ClassSums.lean).

**Definition (Compact mean).** Let $\rho$ be smooth and $H \subseteq G$ a compact subgroup. The *mean* of $x \in V$ over $H$ is the class integral, over the trivial group and the whole group $H \times H$, of $(a, b) \mapsto \rho(a^{-1}b)x$.

Lean: `New.compactMean` (Lib/Adelic/Hecke/ClassSums.lean).

**Lemma.** The mean of $x$ over $H$ is $H$-fixed. If $x$ is $H$-fixed, its mean is $x$.

Lean: `New.compactMean_mem_levelSpace`, `New.compactMean_eq_self` (Lib/Adelic/Hecke/ClassSums.lean).

The orbit map of a smooth vector has an open stabilizer, so the class integral is a finite average over the finite quotient $H \times H / \operatorname{Stab}$. Right translation in either factor permutes this quotient, which gives the invariance. The definition is irreducible in Lean, so the later proofs use only these lemmas.

### Where the argument uses these objects

The class sum is the most used object of this chapter. It appears in about thirty files of the argument: in the inner products of algebraic forms ([theta kernels and gauges](/chapter/theta-kernels-gauges/), [divisibility](/chapter/divisibility/), [archimedean size](/chapter/archimedean-size/)), in the counts of [Poincaré series](/chapter/poincare-series/), and in the integrality of [integral target forms](/chapter/integral-target-forms/). The class integral enters the [seesaw identity](/chapter/seesaw-identity-2/) and the lift chains of [the objects of the upper bound](/chapter/upper-bound-objects/) in Theorem A, the paths of [grids, paths and turns](/chapter/grids-paths-turns/), the spanning forms of [deep level Poincaré series](/chapter/deep-level-poincare/), one exchange of [the comparison operator](/chapter/comparison-operator-1/), and the lattices of corank of [the remaining terms](/chapter/remaining-terms/). The Hecke operator is applied directly at a split place in the Hecke edges of [divisibility](/chapter/divisibility/). The compact mean is used once, in the grids of [grids, paths and turns](/chapter/grids-paths-turns/), to project a vector onto the vectors fixed by the chosen level.
