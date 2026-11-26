---
title: Bad types at the level primes
lean:
  - New/Spanning/SecondMoment/SpanningTheorem.lean
  - New/Spanning/MainTerm/BadTypes.lean
  - New/UpperBound/Objects/LabelsAndIndexTypes.lean
decls:
  - New.Data.levelRepresentation
  - New.Data.levelRepresentation_apply
  - New.Data.inner_levelRepresentation
  - New.Data.goodIdempotentAbove
  - New.Data.isCentralProj_goodIdempotentAbove
  - New.Data.levelRepresentation_goodIdempotentAbove_eq
  - New.Data.re_coeff_one_sub_goodIdempotentAbove_le
  - New.Data.bad_types_rare
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Bad types at the level primes

The near isometry of [the chapter on moments](/chapter/moments/#good-forms) is a theorem about general filling data $S$. Its group is $S.\mathtt{ResidueGL}$, the product over the two level primes $p_0, p_1$ of the groups $\prod_{w \mid p_i}\mathrm{GL}_r(\mathbb{F}_w)$. Its projection is a tensor product $g_0 \otimes g_1$ of central idempotents, one for each level prime. The data $D$ has the group $\bar G = D.\mathtt{chosenGL}$, one product over all chosen places, and the idempotent $e_0$, one sum over families of labels. This section matches the two settings and proves the hypothesis on $g_0, g_1$ for $D$. It is the application of [the theorem on bad types](/chapter/equal-multiplicities/#bad-types-are-rare) that the section on bad types announces.

### The group sorted by primes

The two groups have the same elements up to the order of the indices. An element of $\bar G$ is a function on the pairs $(i, w)$ with $w$ a chosen place above $p_i$. An element of $S.\mathtt{ResidueGL}$, for $S = D.\mathtt{filling}$, is a function of $i$ whose value is a function of $w$. The map `Sigma.uncurry` turns the second form into the first.

**Definition (The level representation).** The level representation is the representation of $D.\mathtt{filling}.\mathtt{ResidueGL}$ on the forms of principal level on $Y_0$ given by $s \mapsto D.\mathtt{principalRep}\,(\mathtt{Sigma.uncurry}\ s)$.

Lean: `New.Data.levelRepresentation` (New/Spanning/SecondMoment/SpanningTheorem.lean).

**Lemma (The level representation at an element).** For each $s$, the operator of $s$ in the level representation is the operator of $\mathtt{Sigma.uncurry}\ s$ in $D.\mathtt{principalRep}$.

Lean: `New.Data.levelRepresentation_apply` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* This is the definition. $\square$

**Lemma (The level representation is unitary).** For each $s$ and all forms $x, y$ of principal level on $Y_0$, $\langle s x, s y\rangle = \langle x, y\rangle$.

Lean: `New.Data.inner_levelRepresentation` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* An element of $\bar G$ acts by the right translation by an integral lift. The Petersson inner product is invariant under right translation by an element of the finite adelic group (`Space.inner_formRep`). $\square$

### The two idempotents

Let $q_2 = P.\mathtt{q₂}\ D.\mathtt{towerExp}$ and $r = \#\mathtt{RowIndex}$. For a level prime $p_i$, a tuple $c = (c_w)$ of monic polynomials of degree $r$, one over each residue field $\mathbb{F}_w$ with $w$ a chosen place above $p_i$, is *good* if each $c_w$ is allowed for $q_2$ and $r$ and some $c_w$ is primitive (`goodTuples`). [The section on bad types](/chapter/equal-multiplicities/#bad-types-are-rare) gives the words *allowed* and *primitive*.

**Definition (The good idempotent above a level prime).** For $i \in \{0, 1\}$, $e_{p_i}$ is the sum, over the good tuples $c$ for $q_2$ and $r$, of the tensor product $\bigotimes_w e_{c_w}$ of the idempotents of Green's characters of the labels $c_w$. It is an element of the complex group algebra of $\prod_{w \mid p_i}\mathrm{GL}_r(\mathbb{F}_w)$.

Lean: `New.Data.goodIdempotentAbove` (New/Spanning/SecondMoment/SpanningTheorem.lean).

**Lemma (The good idempotent is central).** Each $e_{p_i}$ is a central idempotent: it is idempotent, and its coefficients are a class function.

Lean: `New.Data.isCentralProj_goodIdempotentAbove` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* A sum over a finite set of tuples of the tensor products of the idempotents of Green's characters is a central idempotent ([Theorem](/decl/New.isCentralProj_sum_tupleIdem/)). $\square$

**Lemma (The tensor product acts as the projection onto the good forms).** The tensor product $e_{p_0} \otimes e_{p_1}$ acts through the level representation as $e_0$ acts through $D.\mathtt{principalRep}$:

$$\rho_{\mathrm{level}}(e_{p_0} \otimes e_{p_1}) = \rho(e_0).$$

Lean: `New.Data.levelRepresentation_goodIdempotentAbove_eq` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* An element $a$ of a group algebra acts as $\sum_g a(g)\rho(g)$ (`asAlgebraHom_eq_sum`). So it suffices to match the coefficients of the two elements along the bijection `Equiv.piCurry` between $\bar G$ and $D.\mathtt{filling}.\mathtt{ResidueGL}$. The coefficient of the tensor product at $s$ is a product of two sums, one for each $i$. Expand the product of sums into a sum over pairs (`Finset.prod_univ_sum`):

$$(e_{p_0} \otimes e_{p_1})(s) = \sum_{c} \prod_{i \in \{0,1\}}\ \prod_{w \mid p_i} e_{c_i(w)}(s_i(w)),$$

where $c = (c_0, c_1)$ runs over the pairs of good tuples. The element $e_0$ is the sum of $\bigotimes_{(i,w)} e_{c(i,w)}$ over the good families (`goodTupleFamilies`). A family is good exactly when both of its parts $c_i = c(i, \cdot)$ are good tuples. The product over the pairs $(i, w)$ splits as a product over $i$ and then over $w$ (`prod_sigma`). So the coefficient of $e_0$ at $t$ is the same sum, with $t(i, w)$ in place of $s_i(w)$. The two sums agree when $t = \mathtt{Sigma.uncurry}\ s$, by the lemma on the level representation at an element and the definition of `Sigma.uncurry`. $\square$

### The share of the bad types

**Lemma (Bad types are rare above one level prime).** For $i \in \{0, 1\}$,

$$\operatorname{Re}\bigl((1 - e_{p_i})(1)\bigr) \leq \frac{b^{-8}}{2}.$$

Lean: `New.Data.re_coeff_one_sub_goodIdempotentAbove_le` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* Apply [Theorem](/decl/New.re_coeff_one_sub_sum_tupleIdem_le/) with these values.

| Letter of the theorem | Value |
|---|---|
| $k_w$ | the residue field at the chosen place $w$ above $p_i$ |
| $q$ | $p_i$ |
| $M$ | $q_2$ |
| $r$ | $\#\mathtt{RowIndex}$ |
| $f$ | $D.f$, the number of infinite places of $E$ |
| $\varepsilon$ | $(1 + q_2 + 2r)/p_i$ |
| $L$ | $9\log b$ |

Its hypotheses hold for $D$, as follows.

1. Each $k_w$ has $p_i$ elements (`card_resField_eq_levelPrime`).
2. The number of chosen places above $p_i$ is $D.f$ (`card_chosenPlaces`, from `card_chosenPlace`).
3. $1 < r$ and $r < p_i$. These are size bounds of $D$ (`nat_lt_of_hasLogBound`).
4. $\varepsilon \leq 1$. This is a size bound of $D$ (`le_of_hasLogBound`).
5. $(1 + q_2 + 2r)/p_i \leq \varepsilon$. This is equality.
6. $2r(2r\log p_i + 1)\cdot 9\log b \leq f$. This is a size bound of $D$ (`le_of_hasLogBound`).

The theorem gives $\operatorname{Re}((1 - e_{p_i})(1)) \leq f\varepsilon + e^{-9\log b}$. One more size bound of $D$ is

$$D.f \cdot \frac{1 + q_2 + 2r}{p_i} + e^{-9\log b} \leq \frac{b^{-8}}{2}.$$

The two inequalities give the claim. $\square$

The size bound in the last step asks that $p_i$ is much larger than $f(1 + q_2 + 2r)b^8$. [The primes, the level and the period](/chapter/data-and-sizes/#the-primes-the-level-and-the-period) gives the bounds for $p_0$ and $p_1$ that make this true. The second term $e^{-9\log b} = b^{-9}$ is the share of the tuples with no primitive member. It is small because $f$ is large against $r^2\log p_i \log b$, which is hypothesis 6.

**Theorem (Bad types are rare).** The three facts hold together.

1. Each $e_{p_i}$ is a central idempotent.
2. $\rho_{\mathrm{level}}(e_{p_0} \otimes e_{p_1}) = \rho(e_0)$.
3. For each $i$, $\operatorname{Re}((1 - e_{p_i})(1)) \leq b^{-8}/2$.

Lean: `New.Data.bad_types_rare` (New/Spanning/SecondMoment/SpanningTheorem.lean).

*Proof.* The three lemmas above. $\square$

**Remark (Formalization).** The coefficient of $1 - e_{p_i}$ at the identity is a complex number, and the bound is on its real part. The coefficient is in fact real and nonnegative, since $1 - e_{p_i}$ is a central idempotent and its coefficient at $1$ is the share of its image in the regular representation. The source does not need this. The near isometry of chapter 13 asks only for the bound on the real part, and this theorem gives exactly that hypothesis.

**Remark (Formalization).** The constant $b^{-8}/2$ is not the constant of the plan in one step. [The section on the four layers](/chapter/theorem-b-plan/#the-four-layers-of-the-proof) speaks of a share $b^{-8}$ of bad types. The source asks $b^{-8}/2$ at each of the two primes. The proof of [the good forms theorem](/chapter/moments/#good-forms) turns each share into the bound $\|(1 - e_{p_i})P\|^2 \leq 2b^{-4}D_X$, and the two primes give $4b^{-4}D_X$.

### The constants at the level primes

| Quantity | Bound | Source of the bound |
|---|---|---|
| $\operatorname{Re}((1 - e_{p_i})(1))$ | $\leq f\varepsilon + b^{-9}$ | the theorem on bad types at one prime |
| $f\varepsilon + b^{-9}$ | $\leq b^{-8}/2$ | a size bound of $D$ |
| $\|(1 - e_0)P\|^2$ | $\leq 4b^{-4}D_X$ | [Theorem](/decl/New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_one_sub_piTensorElem_comp_sq_le/) |

The last row is used in the next section.
