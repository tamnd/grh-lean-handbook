---
title: The modulus and the generalised index
lean:
  - Lib/General/Measure/HaarModulus.lean
decls:
  - New.HasStableLifts
  - New.measure_smul_map_restrict_eq_smul_inv
  - New.inv_distribHaarChar_eq_relIndex_div
  - New.map_const_smul_eq_inv_distribHaarChar_smul
  - New.genIndex
  - New.genIndex_eq_card
  - New.distribHaarChar_eq_one_of_mem_intGL
  - New.distribHaarChar_diagGL
  - New.inv_distribHaarChar_GL_eq_genIndex_det
  - New.one_le_genIndex
  - New.genIndex_star
  - New.submoduleIndex_colLattice_div
  - New.submoduleIndex_colLattice_intVectors
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The modulus and the generalised index

An automorphism of a locally compact abelian group multiplies Haar measure by a positive constant, its modulus. On a local field the modulus of multiplication by $a$ is the normalised absolute value $|a|$. On $F^n$ the modulus of a matrix $g$ is $|\det g|$. This section states these facts for the rings of the source. The rings include the finite adeles. The source does not use absolute values. It uses an index: for a unit $a$ and a compact open subring $O$, the number $|O/aO|$. This index replaces $|a|^{-1}$ in the unfolding computations, where volumes of lattices must be computed exactly.

### The modulus as a ratio of indices

Let $A$ be a locally compact abelian group with Haar measure $\mu$. Let a group $G$ act on $A$ by continuous additive automorphisms. For $g \in G$, the measure $s \mapsto \mu(g s)$ is again a Haar measure. So there is a positive real number $\Delta_A(g)$ with
$$\mu(g s) = \Delta_A(g)\, \mu(s)$$
for every Borel set $s$. The number does not depend on $\mu$, and $g \mapsto \Delta_A(g)$ is a homomorphism to $\mathbb{R}_{>0}$. This is the module of Weil (*Basic Number Theory*, Ch. I, §2) and Bourbaki (*Intégration*, Ch. VII, §1). Mathlib calls it the Haar character of the action.

For subgroups $H$ and $K$ of $A$, write $[K : H \cap K]$ for the index of $H \cap K$ in $K$.

**Theorem.** Let $A$ be a locally compact Polish abelian group and let $G$ act on $A$ by continuous additive automorphisms. Let $L \leq A$ be a compact open subgroup and let $g \in G$. Then
$$\Delta_A(g)^{-1} = \frac{[L : gL \cap L]}{[gL : gL \cap L]}.$$

Lean: `New.inv_distribHaarChar_eq_relIndex_div` (Lib/General/Measure/HaarModulus.lean).

*Proof.* The group $gL \cap L$ is open in the compact groups $L$ and $gL$. So it has finite index in both. Then $\mu(L) = [L : gL \cap L]\, \mu(gL \cap L)$ and $\mu(gL) = [gL : gL \cap L]\, \mu(gL \cap L)$. Also $\mu(gL) = \Delta_A(g) \mu(L)$. Divide the two equations. The measure of $gL \cap L$ is positive and finite, so it cancels. $\square$

If $gL \subseteq L$, the theorem gives $\Delta_A(g)^{-1} = [L : gL]$. This is the form in which the source uses it.

**Corollary.** Let $\nu$ be a Haar measure on $A$ and let $a \in G$. The image of $\nu$ under $x \mapsto a x$ is $\Delta_A(a)^{-1} \nu$.

Lean: `New.map_const_smul_eq_inv_distribHaarChar_smul` (Lib/General/Measure/HaarModulus.lean).

*Proof.* The image measure gives the set $s$ the mass $\nu(a^{-1} s) = \Delta_A(a)^{-1} \nu(s)$. $\square$

### The generalised index

Let $R$ be a locally compact commutative ring. Multiplication by a unit $a$ is an automorphism of the additive group of $R$.

**Definition (Generalised index).** For $a \in R$, let
$$\iota(a) = \begin{cases} \Delta_R(a)^{-1} & \text{if } a \text{ is a unit of } R, \\ 0 & \text{otherwise.} \end{cases}$$
Then $\iota$ is multiplicative.

Lean: `New.genIndex` (Lib/General/Measure/HaarModulus.lean).

The value at a unit is positive. The function $\iota$ is a multiplicative character of the monoid $R$. For a unit, the theorem above gives $\iota$ as a ratio of indices (`New.genIndex_eq_relIndex_div`).

**Remark (Formalization).** The value $0$ at a non-unit is a convention. It comes from the way Mathlib extends a homomorphism on the units to a multiplicative character of the ring. For a non-discrete field, the only non-unit is $0$, and multiplication by $0$ sends every set to a set of measure $0$. So the convention agrees with the scaling in this case. For the finite adeles, an element with one component $0$ is a non-unit, and the convention again gives $0$. The source proves no statement about $\iota$ at a non-unit except through the character laws. Each theorem below that uses $\iota$ at a determinant has the determinant of an invertible matrix, which is a unit. So no theorem below depends on the convention.

**Proposition.** Let $O$ be a compact open subring of $R$. Let $a \in O$ be a unit of $R$. Then $\iota(a) = |O / aO|$.

Lean: `New.genIndex_eq_card` (Lib/General/Measure/HaarModulus.lean).

*Proof.* Take $L = O$ in the theorem. Since $aO \subseteq O$, the denominator is $1$ and the numerator is the index of the ideal $aO$ in $O$. $\square$

**Example.** Let $R = \mathbb{Q}_p$ and $O = \mathbb{Z}_p$. For $a = p^k u$ with $u \in \mathbb{Z}_p^\times$ and $k \geq 0$, the quotient $\mathbb{Z}_p / p^k \mathbb{Z}_p$ has $p^k$ elements. So $\iota(a) = p^k = |a|_p^{-1}$ and $\Delta_{\mathbb{Q}_p}(a) = |a|_p$. By multiplicativity the same holds for $k < 0$. For the finite adeles with $O = \widehat{\mathbb{Z}}$, the index $\iota(a)$ is the product of the local indices.

### The modulus of a matrix

The group $\mathrm{GL}_n(R)$ acts on $R^n$, and this action is continuous. Let $O \subseteq R$ be a subring. Recall from the second section of this chapter the group $\mathrm{GL}_n(O)$ of invertible matrices whose inverse also has entries in $O$.

**Lemma.** Let $O$ be a compact open subring of $R$ and let $k \in \mathrm{GL}_n(O)$. Then $\Delta_{R^n}(k) = 1$. Also $\iota(\det k) = 1$.

Lean: `New.distribHaarChar_eq_one_of_mem_intGL` (Lib/General/Measure/HaarModulus.lean). The second statement is `New.genIndex_det_eq_one`.

*Proof.* The matrix $k$ maps the compact open subgroup $O^n$ onto itself. So both indices in the theorem are $1$. The determinant of $k$ is a unit of $O$, so $\det k \cdot O = O$. $\square$

**Lemma.** Let $d_1, \ldots, d_n$ be units of $R$ and let $D$ be the diagonal matrix with these entries. Then
$$\Delta_{R^n}(D) = \prod_{i=1}^n \Delta_R(d_i).$$

Lean: `New.distribHaarChar_diagGL` (Lib/General/Measure/HaarModulus.lean).

*Proof.* Let $C$ be a compact set of positive measure in $R$. The matrix $D$ maps the box $C^n$ onto the product of the sets $d_i C$. Compare the product measures of the two boxes. $\square$

To pass from diagonal matrices to all matrices, one needs a Smith form. The source states the property of $O$ that gives it.

**Definition (Valuation pair).** A subring $O$ of a commutative ring $R$ is a [valuation pair](/decl/New.IsValuationPair/) if for all $a, b \in R$ there is an idempotent $e \in O$ such that $a$ and $b$ are both $O$-multiples of $(1 - e) a + e b$.

Lean: `New.IsValuationPair` (Lib/General/LinearAlgebra/IntegralLattices.lean).

For a valuation ring $O$ with fraction field $R$, take $e = 0$ or $e = 1$: one of $a$ and $b$ divides the other. For a product of valuation rings, take $e$ componentwise. So $\widehat{\mathbb{Z}} \subseteq \mathbb{A}_f$ is a valuation pair.

**Theorem.** Let $R$ be a locally compact Polish commutative ring. Let $O$ be a compact open subring that is a valuation pair. Then for every $g \in \mathrm{GL}_n(R)$,
$$\Delta_{R^n}(g)^{-1} = \iota(\det g).$$

Lean: `New.inv_distribHaarChar_GL_eq_genIndex_det` (Lib/General/Measure/HaarModulus.lean).

*Proof.* By the Smith form for a valuation pair, $g = k D k'$ with $k, k' \in \mathrm{GL}_n(O)$ and $D$ diagonal. The entries of $D$ are units because $\det g$ is a unit. Both sides of the claim are multiplicative in $g$. Both are $1$ on $\mathrm{GL}_n(O)$ by the first lemma. On $D$ they agree by the second lemma and the multiplicativity of $\iota$. $\square$

For a field with $O$ the valuation ring, this is the classical formula $\Delta_{F^n}(g) = |\det g|$. Over a principal ideal domain, the Smith form is the theorem on elementary divisors (Lang, *Algebra*, Ch. III, §7).

**Remark (Formalization).** The Smith form of the source is `New.IsValuationPair.smith_normal_form` in Lib/General/LinearAlgebra/IntegralLattices.lean. Its statement gives $g = k D k'$ with $D$ diagonal, and states no divisibility among the diagonal entries. The classical theorem also gives $d_1 \mid d_2 \mid \cdots \mid d_n$. The proof above does not need this condition, so the weaker statement is enough. The docstring of the lemma says so.

### Lattices

Now let $A$ be a commutative ring with an involution, and let $R \subseteq A$ be a subring. The source collects the properties of $\widehat{\mathbb{Z}} \subseteq \mathbb{A}_f$, or of $\widehat{\mathcal{O}}_E \subseteq \mathbb{A}_{E,f}$ for an imaginary quadratic field $E$, in the class of adelic pairs (`New.IsAdelic`). Its fields say: $R$ is open, compact and stable under the involution; $R$ is a valuation pair; some $i \in R$ has $-i^2 = 1$ and $\bar\imath = -i$, and some $\tau \in R$ has $\tau + \bar\tau = 1$; and $-1 = \bar c c$ for some $c \in R$. This section uses only that $R$ is open, compact, stable under the involution and a valuation pair.

**Proposition.** Assume that $R \subseteq A$ has these properties. Then $\iota(u) \geq 1$ for every $u \in R$ that is a unit of $A$. Also $\iota(\bar a) = \iota(a)$ for every $a \in A$.

Lean: `New.one_le_genIndex` (Lib/General/Measure/HaarModulus.lean). The second statement is `New.genIndex_star`.

*Proof.* For the first claim, $\iota(u) = |R/uR|$ is a positive integer. For the second, the involution is a homeomorphism that maps $R$ onto $R$ and $\bar b R$ onto $b R$. So it preserves the two indices in the theorem. A non-unit maps to a non-unit, and both sides are $0$. $\square$

For $M \in \mathrm{GL}_n(A)$, let $\Lambda_M$ be the $R$-span of the columns of $M$, and let $\Lambda_0 = R^n$. Then $\Lambda_M = M \Lambda_0$.

**Theorem.** Assume that $R \subseteq A$ has the properties above, and let $M \in \mathrm{GL}_n(A)$. Then
$$\frac{[\Lambda_0 : \Lambda_M \cap \Lambda_0]}{[\Lambda_M : \Lambda_M \cap \Lambda_0]} = \iota(\det M).$$
If $M$ has entries in $R$, then $[\Lambda_0 : \Lambda_M] = \iota(\det M)$.

Lean: `New.submoduleIndex_colLattice_div` (Lib/General/Measure/HaarModulus.lean). The second statement is `New.submoduleIndex_colLattice_intVectors`.

*Proof.* Apply the index theorem with $L = \Lambda_0$ and $g = M$, and then the theorem on matrices. If $M$ has entries in $R$, then $\Lambda_M \subseteq \Lambda_0$, and the denominator is $1$. $\square$

**Remark (Formalization).** The index in these statements is `New.submoduleIndex`, which is Mathlib's relative index of the underlying subgroups. Mathlib gives an infinite index the value $0$. Here both lattices are compact and open, so both indices are finite and the convention does not occur. In the first statement the indices are cast to real numbers before the division. A zero denominator would make the quotient $0$, but the denominator is a positive integer.

### Pushforward of a Haar measure

The last result compares a Haar measure on a group $Z$ with its image on a quotient group $G$. The source uses it to prove that a unitary group over a product of completions is unimodular.

**Proposition.** Let $\mu$ be a left and right invariant s-finite measure on a group $Z$. Let $\eta$ be a left invariant s-finite measure on a group $G$, and let $\pi : Z \to G$ be a measurable homomorphism. Let $O \subseteq Z$ be measurable, and assume that every $h \in G$ has a lift $g \in Z$ with $gO = O$ and $Og = O$. Then for every measurable $K \subseteq G$,
$$\eta(K) \cdot \pi_*(\mu|_O) = \mu(\pi^{-1}(K) \cap O) \cdot \check\eta,$$
where $\check\eta$ is the image of $\eta$ under $x \mapsto x^{-1}$.

Lean: `New.measure_smul_map_restrict_eq_smul_inv` (Lib/General/Measure/HaarModulus.lean). The condition on the lifts is `New.HasStableLifts`.

*Proof.* The condition on the lifts makes $\nu = \pi_*(\mu|_O)$ left invariant, and it gives every right translate of $K$ the $\nu$-measure $\mu(\pi^{-1}(K) \cap O)$. The formula $\eta(K) \int f \, d\nu = \int \nu(\{z : z x \in K\}) f(x^{-1}) \, d\eta(x)$ for two left invariant measures then gives the claim. $\square$

In the typical case $\eta(K)$ is finite and positive. Then the proposition says that $\pi_*(\mu|_O)$ is a multiple of $\check\eta$, with an explicit constant. If $\eta(K) = 0$ or $\eta(K) = \infty$, the identity holds but gives no information about $\pi_*(\mu|_O)$.
