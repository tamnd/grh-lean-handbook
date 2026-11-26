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

This section gives two finite sums: the Hecke operator, a sum of translates over cosets in $G/K$, and the class sum over $\Gamma \backslash G / K$, which on a definite group is the integral over the quotient (Section 2). The source defines both for an arbitrary group, with no measure, and gives every sum a value.

Throughout, $G$ is a group, $\Gamma$ and $K$ are subgroups of $G$, $A$ is a commutative ring, and $\pi$ is a representation of $G$ on an $A$-module $W$.

### Fixed vectors and Hecke operators

**Definition (Right regular representation).** The *right regular representation* of $G$ on the functions $F : G \to W$ is $(g \cdot F)(x) = F(xg)$.

Lean: `New.rightRegular` (Lib/Adelic/Hecke/Basic.lean).

**Definition (Level space).** For a character $\chi : K \to A^\times$, the *level space* of $(K, \chi)$ is the submodule of the $v \in W$ with $\pi(k)v = \chi(k)v$ for all $k \in K$. For $\chi = 1$ it is the space $W^K$ of $K$-fixed vectors.

Lean: `New.levelSpace` (Lib/Adelic/Hecke/Basic.lean).

The default $\chi$ is trivial. For right translation, $W^K$ is the set of functions of level $K$ (Section 1).

**Definition (Hecke operator).** For $f : G \to A$, the *Hecke operator* of $f$ is $\pi(f) = \sum_{q \in G/K} f(g_q)\pi(g_q)$, where $g_q$ is a chosen representative of the coset $q$. The source sets $\pi(f) = 0$ if infinitely many terms are nonzero. The Hecke operator of the double coset $KgK$ is $\pi(\mathbf{1}_{KgK})$.

Lean: `New.heckeFun`, `New.heckeCoset` (Lib/Adelic/Hecke/Basic.lean).

**Definition (Hecke function).** The function $f$ *has finite cosets* if $f(g_q) \neq 0$ for only finitely many $q \in G/K$. It is a *Hecke function* for $K$ if it has finite cosets and $f(gk) = f(kg) = f(g)$ for all $g \in G$ and $k \in K$.

Lean: `New.HasFiniteCosets`, `New.IsHeckeFunction` (Lib/Adelic/Hecke/Basic.lean).

**Lemma.** Let $G$ be a topological group and $K$ a compact open subgroup. For every $g \in G$ the indicator function of $KgK$ is a Hecke function for $K$.

Lean: `New.isHeckeFunction_doubleCoset` (Lib/Adelic/Hecke/Basic.lean).

*Proof.* The set $KgK$ is compact, as the image of $K \times K$. The open cosets $xK$ with $x \in KgK$ cover it, so finitely many do. The indicator is $K$-invariant on both sides. $\square$

**Remark (Formalization).** The representative $g_q$ is `q.out`, a choice. The textbook operator $\int f(g)\pi(g)\,dg$, with $\operatorname{vol}(K) = 1$, acts on $W^K$; the source's acts on all of $W$. They agree on $W^K$ for right $K$-invariant $f$ by the next lemma, the only case the argument uses. Each use proves that $f$ has finite cosets, so the junk value $0$ (finding F-036) does not occur.

**Lemma (Any representatives serve).** Let $f(gk) = f(g)$ for all $g \in G$ and $k \in K$, and let $v \in W^K$. Let $(r_i)_{i \in s}$ be a finite family in $G$ whose cosets $r_i K$ are distinct and cover the support of $f$. Then $f$ has finite cosets, and $\pi(f)v = \sum_{i \in s} f(r_i)\pi(r_i)v$.

Lean: `New.heckeFun_eq_sum` (Lib/Adelic/Hecke/Basic.lean).

*Proof.* If $f(g_q) \neq 0$, then $q = r_i K$ for some $i \in s$, so $f$ has finite cosets. The representative of $gK$ is $gk$ with $k \in K$, and $f(gk)\pi(gk)v = f(g)\pi(g)v$ because $f$ is right $K$-invariant and $v$ is $K$-fixed. So each term over $G/K$ is the term at the unique $r_i$ with $q = r_iK$, or $0$. $\square$

**Lemma (Composition).** Let $f$ and $f'$ have finite cosets, let $f$ be right $K$-invariant, and let $v \in W^K$. Let $Q$ be the finite set of cosets $q$ with $f'(g_q) \neq 0$. Then $\pi(f')\pi(f)v = \pi(f' * f)v$, where $(f' * f)(x) = \sum_{q \in Q} f'(g_q)\, f(g_q^{-1}x)$.

Lean: `New.heckeFun_heckeFun` (Lib/Adelic/Hecke/Basic.lean).

*Proof.* The cosets $g_q g_p K$, for $p \in G/K$, run once over $G/K$. So by the lemma above, $\pi(g_q)\pi(f)v$ is the operator of $x \mapsto f(g_q^{-1}x)$ applied to $v$. Sum over $q \in Q$ with weights $f'(g_q)$ and use linearity. $\square$

**Lemma.** Let $f$ be a Hecke function for $K$ and $v \in W^K$. Then $\pi(f)v \in W^K$.

Lean: `New.IsHeckeFunction.heckeFun_mem` (Lib/Adelic/Hecke/Basic.lean).

*Proof.* By the composition lemma with $f'$ the indicator of $kK$, $\pi(k)\pi(f)v$ is the operator of $x \mapsto f(k^{-1}x) = f(x)$ applied to $v$. $\square$

### Class sums

**Definition (Stabilizer, double cosets).** For $g \in G$, the group $\Gamma \cap gKg^{-1}$ is the *stabilizer* of $g$, the subgroup of $\Gamma$ that fixes the point $gK$ of $G/K$. The set $\Gamma \backslash G / K$ is the set of double cosets $\Gamma g K$.

Lean: `New.classAut`, `New.DoubleCosets` (Lib/Adelic/Hecke/Basic.lean).

The order of the stabilizer depends only on the double coset: $\#(\Gamma \cap (\gamma g k)K(\gamma g k)^{-1}) = \#(\Gamma \cap gKg^{-1})$ for $\gamma \in \Gamma$ and $k \in K$, by conjugation with $\gamma^{-1}$.

Lean: `New.card_classAut_mul_mul` (Lib/Adelic/Hecke/Basic.lean).

**Definition (Class sum).** Let $W$ be a $\mathbb{Q}$-vector space and $f : G \to W$. The *class sum* of $f$ is
$$\Sigma_{\Gamma, K}(f) = \sum_{c \in \Gamma \backslash G / K} \frac{f(g_c)}{\#(\Gamma \cap g_c K g_c^{-1})},$$
where $g_c$ is a chosen representative of $c$.

Lean: `New.classSum` (Lib/Adelic/Hecke/Basic.lean).

If $f$ is left $\Gamma$-invariant and right $K$-invariant, any system of representatives of $\Gamma \backslash G / K$ gives the same sum.

Lean: `New.classSum_eq_finsum_of_rep` (Lib/Adelic/Hecke/Basic.lean).

**Remark (Formalization).** The sum is `finsum`, which is $0$ for infinitely many nonzero terms. The order is `Nat.card`, which is $0$ for an infinite group, and $0^{-1} = 0$. The source states these junk values in the file header. Every theorem that makes a class sum an integral, a dimension or a positive number assumes the next condition.

**Definition (Finite type).** The pair $(\Gamma, K)$ *has finite type* if $G$ is a topological group, $K$ is compact and open, $\Gamma \backslash G / K$ is finite, and every stabilizer $\Gamma \cap gKg^{-1}$ is finite.

Lean: `New.HasFiniteType` (Lib/Adelic/Hecke/ClassSums.lean).

For $V$ with all signs $+1$ and a level $K$, $(\Gamma_{V,f}, K)$ has finite type: `New.Space.hasFiniteType_of_isLevel` (Lib/Adelic/Reduction/DefiniteClassSums.lean), from [reduction theory](/chapter/reduction-theory/).

**Lemma.** If $(\Gamma, K)$ has finite type and $K' \subseteq K$ is an open subgroup, then $(\Gamma, K')$ has finite type.

Lean: `New.HasFiniteType.of_le` (Lib/Adelic/Hecke/ClassSums.lean).

*Proof.* $[K:K']$ is finite, each class for $K'$ is $\Gamma g q K'$ with $q \in K/K'$, stabilizers shrink, and $K'$ is closed, so compact. $\square$

**Lemma.** Let $(\Gamma, K)$ have finite type, and let all stabilizers be trivial. Then $\Sigma_{\Gamma, K}(1) = \#(\Gamma \backslash G / K)$, as real numbers.

Lean: `New.card_classes_eq_classSum` (Lib/Adelic/Hecke/ClassSums.lean).

**Lemma (Positivity).** Let $(\Gamma, K)$ have finite type, let $W$ be an ordered $\mathbb{Q}$-vector space, and let $f \geq 0$ with $f(g_c) > 0$ for some class $c$. Then $\Sigma_{\Gamma, K}(f) > 0$.

Lean: `New.classSum_pos` (Lib/Adelic/Hecke/ClassSums.lean).

*Proof.* The sum is finite, each weight is positive since each stabilizer is finite and nonempty, and one term is positive. $\square$

### The class integral

**Definition (Class integral).** For $f : G \to W$, let $\operatorname{Stab}(f)$ be the subgroup of $k \in G$ with $f(gk) = f(g)$ for all $g$. The *class integral* of $f$ at $(\Gamma, K)$ is
$$I_{\Gamma, K}(f) = [K : K \cap \operatorname{Stab}(f)]^{-1}\, \Sigma_{\Gamma, K \cap \operatorname{Stab}(f)}(f).$$

Lean: `New.rightStabilizer`, `New.classIntegral` (Lib/Adelic/Hecke/ClassSums.lean).

For finite type and $f$ left $\Gamma$-invariant with open stabilizer, $I_{\Gamma,K}(f)$ is the integral over $\Gamma \backslash G$ with $\operatorname{vol}(K) = 1$. Section 7 proves the match with the measure-theoretic integral on the standard definite space.

**Remark (Formalization).** The index is `Subgroup.relIndex`, which is $0$ if infinite, and then $I_{\Gamma,K}(f) = 0$. The theorems assume an open stabilizer, so this junk value does not reach the argument.

**Lemma.** If $K \subseteq \operatorname{Stab}(f)$, then $I_{\Gamma,K}(f) = \Sigma_{\Gamma,K}(f)$.

Lean: `New.classIntegral_eq_classSum` (Lib/Adelic/Hecke/ClassSums.lean).

*Proof.* Then $K \cap \operatorname{Stab}(f) = K$ and the index is $1$. $\square$

### Change of level

**Lemma (Transporter).** Let $(\Gamma, K)$ have finite type and $g, h \in G$. The set of $\gamma \in \Gamma$ with $g^{-1}\gamma h \in K$ is finite. It has $\#(\Gamma \cap gKg^{-1})$ elements if $\Gamma g K = \Gamma h K$, and it is empty otherwise.

Lean: `New.exists_transporter` (Lib/Adelic/Hecke/ClassSums.lean).

*Proof.* If $h = agk$ with $a \in \Gamma$ and $k \in K$, then $g^{-1}\gamma h \in K$ if and only if $\gamma \in (\Gamma \cap gKg^{-1})a^{-1}$. Otherwise no $\gamma$ serves. $\square$

**Theorem (Change of level).** Let $(\Gamma, K)$ and $(\Gamma, K')$ have finite type. Let $a \in G$, let $L = a^{-1}K'a$, and suppose $L \subseteq K$. Let $f, F : G \to W$ with $f(g_{\Gamma (ga) K}) = F(g)$ for all $g$, where $g_c$ is the chosen representative of the class $c$. Then
$$\Sigma_{\Gamma, K'}(F) = [K : L]\, \Sigma_{\Gamma, K}(f).$$

Lean: `New.classSum_eq_relIndex_smul` (Lib/Adelic/Hecke/ClassSums.lean).

*Proof.* Let $T_U(y, x) = \{\gamma \in \Gamma : y^{-1}\gamma x \in U\}$. By the transporter lemma, $F(x) = \Sigma_{\Gamma,K}\bigl(y \mapsto \#T_K(y, xa)\, f(y)\bigr)$, since the count cancels the weight. Split by the cosets $q_i L$ of $L$ in $K$: $\#T_K(y, xa) = \sum_{i} \#T_{K'}(yq_ia^{-1}, x)$. Exchange the finite sums; for fixed $y$ and $i$ the class sum over $x$ of $\#T_{K'}(yq_ia^{-1}, x)$ is $1$. $\square$

**Remark (Formalization).** The transporter sets come by `choose`; only their sizes enter. The hypothesis ties $F$ to $f$ at chosen representatives; for invariant $f$ take $F(g) = f(ga)$.

**Corollary.** Let $(\Gamma, K)$ and $(\Gamma, K')$ have finite type with $K' \subseteq K$. Then $\Sigma_{\Gamma,K'}(1) = [K : K']\,\Sigma_{\Gamma,K}(1)$, as real numbers.

Lean: `New.classSum_one_of_le` (Lib/Adelic/Hecke/ClassSums.lean).

*Proof.* Take $a = 1$, $L = K'$, and $f = F = 1$ in the theorem. $\square$

On a definite group $\Sigma_{\Gamma,K}(1)$ is the *mass* of $K$.

### Means over a compact group

**Definition (Unitary form, smooth representation).** Let $\rho$ be a representation of $G$ on a complex vector space $V$. A sesquilinear form $B$ on $V$ is *unitary* for $\rho$ if $B(x, x) > 0$ for $x \neq 0$ and $B(\rho(g)x, \rho(g)y) = B(x, y)$ for all $g$, $x$ and $y$. The representation is *smooth* if every vector is fixed by all $g$ in some neighborhood of $1$.

Lean: `New.IsUnitary`, `New.IsSmoothRep` (Lib/Adelic/Hecke/ClassSums.lean).

**Definition (Compact mean).** Let $\rho$ be smooth and $H \subseteq G$ a compact subgroup. The *mean* of $x \in V$ over $H$ is the class integral, over the trivial group and the whole group $H \times H$, of $(a, b) \mapsto \rho(a^{-1}b)x$.

Lean: `New.compactMean` (Lib/Adelic/Hecke/ClassSums.lean).

**Lemma.** The mean of $x$ over $H$ is $H$-fixed. If $x$ is $H$-fixed, its mean is $x$.

Lean: `New.compactMean_mem_levelSpace`, `New.compactMean_eq_self` (Lib/Adelic/Hecke/ClassSums.lean).

The mean is a finite average, since the orbit map has an open stabilizer. The definition is irreducible, so proofs use only these lemmas.

### Where the argument uses class sums

Class sums: [theta kernels and gauges](/chapter/theta-kernels-gauges/), [divisibility](/chapter/divisibility/), [archimedean size](/chapter/archimedean-size/), [Poincaré series](/chapter/poincare-series/), [integral target forms](/chapter/integral-target-forms/). Class integrals: [seesaw identity](/chapter/seesaw-identity-2/), [upper bound objects](/chapter/upper-bound-objects/), [deep level Poincaré series](/chapter/deep-level-poincare/), [comparison operator](/chapter/comparison-operator-1/), [remaining terms](/chapter/remaining-terms/). Hecke operators: [divisibility](/chapter/divisibility/). Compact means and class integrals: [grids, paths and turns](/chapter/grids-paths-turns/).
