---
title: The standard basis
lean:
  - Lib/GLn/SchurModule/MinorBasis.lean
  - Lib/GLn/SchurModule/Basic.lean
  - Lib/GLn/SchurModule/SchurMatrix.lean
decls:
  - New.GL.ColouredTableau
  - New.GL.minorProduct
  - New.GL.columnWeight
  - New.GL.IsStdMinorFamily
  - New.GL.exists_isStdMinorFamily
  - New.GL.columnOrder
  - New.GL.rowExpansion
  - New.GL.HasLeadingTerm
  - New.GL.interlacing
  - New.GL.degree_rowExpansion_mem_interlacing
  - New.GL.HasLeadingTerm.leadingCoeff_mem_nabla
  - New.GL.exists_bordering
  - New.GL.linearIndependent_of_hasLeadingTerm
  - New.GL.nabla_le_span_of_hasLeadingTerm
  - New.GL.alternant
  - New.GL.alternant_succ
  - New.IsTableauBasis
  - New.exists_isTableauBasis
  - New.isTableauBasis_epsilon
  - New.BasisTableau
  - New.WeylIndexFamily
  - New.nablaBasis
  - New.linearIndependent_nablaBasis
  - New.range_nablaCombination
  - New.GL.nablaCombination
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The standard basis

This section gives the module of semi-invariants of weight $\kappa$ a basis of minor products over every commutative ring. The proof is an induction on the number of rows. It removes one row, reads off the leading term in that row, and puts the row back by bordering the columns.

### The textbook theorem

A filling of a Young diagram is *semistandard* if its entries increase strictly down the columns and weakly along the rows. The *standard basis theorem* of Doubilet, Rota and Stein, in the form of De Concini, Eisenbud and Procesi, Invent. Math. 56 (1980), says that the minor products of the semistandard fillings form a basis of the span of all minor products of the diagram, over $\mathbb Z$. Akin, Buchsbaum and Weyman, Adv. Math. 44 (1982), prove the corresponding statement for Schur modules over any commutative ring. The character is the Schur polynomial $s_\lambda = a_{\lambda + \delta} / a_\delta$ (Fulton and Harris, *Representation Theory*, 1991, Theorem 6.3).

The source proves an existence form of the theorem. It shows that some finite set of fillings has all the properties that the semistandard fillings have. It does not show that this set is the set of semistandard fillings.

### Coloured fillings and the statement

**Definition.** Let the rows $m$ be coloured by $c : m \to \Phi$. Let $J$ be a finite set of columns, with a colour $\tau_j$ and a height $h_j$ for each $j \in J$. A *coloured filling* gives each column $j$ an $h_j$-tuple of rows of colour $\tau_j$. Its *minor product* is $\prod_j \Delta_{I_j}$. The *column weight* of the columns is the weight whose value at $(\tau, i)$ is the number of columns of colour $\tau$ with height greater than $i$.

Lean: `New.GL.ColouredTableau`, `New.GL.minorProduct`, `New.GL.columnWeight` (Lib/GLn/SchurModule/MinorBasis.lean).

The column weight is the diagram weight of Section 2, written for an arbitrary finite set of columns. The source proves that the two agree (`New.GL.diagramWeight_eq_columnWeight`).

**Definition.** A family $I_\iota$, $\iota$ in a finite type, of coloured fillings of the columns $J$ is a *standard minor family* if it has three properties.

1. Over every commutative ring $R$ the minor products of the $I_\iota$ are linearly independent.
2. Over every commutative ring $R$ the module $\nabla(l)$ of semi-invariants of the column weight $l$ lies in the span of these minor products.
3. If there is only one colour $t$, then for every enumeration $e : \{0, \dots, N - 1\} \to m$ of the rows and every $x : m \to \mathbb C$,
$$\Big(\sum_\iota \prod_{j} \prod_{s < h_j} x_{I_\iota(j, s)}\Big) \cdot a_0(x \circ e) = a_{l(t, \cdot)}(x \circ e).$$

Lean: `New.GL.IsStdMinorFamily` (Lib/GLn/SchurModule/MinorBasis.lean).

Here $a_l$ is the alternant of the next definition. The product in property 3 is the monomial $x^{I_\iota}$ of the entries of the filling. So property 3 says that the generating function of the weights of the basis is $a_l / a_0$.

**Definition.** For $x \in \mathbb C^N$ and $l : \mathbb N \to \mathbb N$, the *alternant* $a_l(x)$ is $\det\big(x_i^{\,l(N - 1 - j) + j}\big)_{0 \le i, j < N}$ if $l(N) = 0$, and $0$ otherwise.

Lean: `New.GL.alternant` (Lib/GLn/SchurModule/Basic.lean).

The exponents in column $j$ are $l(N - 1 - j) + j$. For antitone $l$ they are strictly decreasing when read from the right. So $a_l$ is the classical alternant $a_{l + \delta}$ with the columns in reverse order, and $a_0$ is the Vandermonde determinant up to sign. The value $0$ when $l(N) \neq 0$ is a junk value.

**Theorem (standard basis).** Let $m$ be a finite set of rows coloured by $c$, and let $J$ be a finite set of columns with colours $\tau$ and heights $h$. Then there is a finite type $\iota$ and a family $I : \iota \to$ (coloured fillings) that is a standard minor family.

Lean: `New.GL.exists_isStdMinorFamily` (Lib/GLn/SchurModule/MinorBasis.lean).

### Leading terms in one row

The proof needs an order on monomials. Fix a row $y$. Every array polynomial is a polynomial in the variables $X(y, 0), X(y, 1), \dots$ of the row $y$, with coefficients that are polynomials in the other rows.

**Definition.** The *row expansion* at $y$ is the $R$-algebra isomorphism from the array polynomials in the rows $m$ to the polynomials in the variables $X(y, i)$, $i \in \mathbb N$, over the array polynomials in the rows other than $y$. The *column order* is the lexicographic order on the exponents $\gamma : \mathbb N \to \mathbb N$ that compares the exponents at the highest column first. A polynomial $F$ *has leading term* $G \cdot x^\gamma$ if no monomial of $F$ exceeds $x^\gamma$ in the column order and the coefficient of $x^\gamma$ is $G$.

Lean: `New.GL.rowExpansion`, `New.GL.columnOrder`, `New.GL.HasLeadingTerm` (Lib/GLn/SchurModule/MinorBasis.lean).

In `New.GL.HasLeadingTerm` the coefficient $G = 0$ is allowed. Then the statement says only that every monomial of $F$ is at most $x^\gamma$.

**Definition.** For an antitone weight $l$ on $\mathbb N$, the set $\operatorname{Int}(l)$ consists of the $\gamma : \mathbb N \to \mathbb N$ with $\gamma(i) \le l(i) - l(i + 1)$ for all $i$, with truncated subtraction.

Lean: `New.GL.interlacing` (Lib/GLn/SchurModule/MinorBasis.lean).

For an antitone $l$, the number $l(i) - l(i + 1)$ is the number of columns of height exactly $i + 1$. So $\gamma \in \operatorname{Int}(l)$ says that $\mu = l - \gamma$ satisfies $l(i + 1) \le \mu(i) \le l(i)$: the partition $\mu$ interlaces $l$. This is the condition of the classical branching rule from $GL_N$ to $GL_{N - 1}$.

**Lemma.** Let $f$ be a semi-invariant of weight $l$, and let $\gamma$ be the leading exponent of $f$ in the row $y$ for the column order. Then $\gamma \in \operatorname{Int}(l(c(y), \cdot))$.

Lean: `New.GL.degree_rowExpansion_mem_interlacing` (Lib/GLn/SchurModule/MinorBasis.lean).

**Lemma.** Let $\gamma$ be the leading exponent of $f$ in the row $y$, and let $f$ be a semi-invariant of weight $\gamma + l$, with $\gamma$ placed at the colour of $y$. Then the leading coefficient of $f$ in the row $y$ is a semi-invariant of weight $l$ in the other rows.

Lean: `New.GL.HasLeadingTerm.leadingCoeff_mem_nabla` (Lib/GLn/SchurModule/MinorBasis.lean).

Both lemmas come from the semi-invariance under a generic upper triangular matrix, by a comparison of the top coefficients in the column order.

### Bordering

The converse of the two lemmas is a construction. It takes a filling of the other rows and adds the row $y$ to some columns.

**Lemma (bordering).** Let $l$ be the column weight of the columns $J$ with heights $h$, and let $\gamma \in \operatorname{Int}(l(c(y), \cdot))$. Then there are heights $k$ with three properties.

1. The column weight of $h$ is $\gamma$, placed at the colour of $y$, plus the column weight of $k$.
2. For every filling $I$ of the heights $k$ by rows other than $y$, there is a filling $K$ of the heights $h$ such that, over every commutative ring, the minor product of $K$ has leading term $\operatorname{minorProduct}(I) \cdot x_y^\gamma$ in the row $y$.
3. The entries of $K$ are those of $I$ and $|\gamma|$ copies of $y$: for every $x : m \to \mathbb C$, $x^K = x_y^{|\gamma|} x^I$.

Lean: `New.GL.exists_bordering` (Lib/GLn/SchurModule/MinorBasis.lean).

*Proof.* There are $l(i) - l(i + 1)$ columns of colour $c(y)$ and height $i + 1$, and $\gamma(i)$ is at most this number. Lower the height of $\gamma(i)$ of them by one. This gives $k$ and (1). Given $I$, let $K$ be $I$ with the row $y$ appended at the bottom of each lowered column. Expand each bordered minor along its last row. The term of the highest column $i$ is $+\Delta_{I_j} \cdot X(y, i)$, and every other term has a lower variable of the row $y$. Leading terms multiply in a monomial order, which gives (2). (3) is clear from the construction. $\square$

### The proof of the standard basis theorem

Two lemmas pass from leading terms to independence and spanning.

**Lemma.** Let $p_{\gamma, i}$ be polynomials, for $\gamma$ in a finite set $\Gamma$ of exponents and $i$ in index types $\iota_\gamma$. Suppose that $p_{\gamma, i}$ has leading term $q_{\gamma, i} \cdot x_y^\gamma$ in the row $y$, and that for each $\gamma$ the family $q_{\gamma, \cdot}$ is linearly independent. Then the family of all $p_{\gamma, i}$ is linearly independent.

Lean: `New.GL.linearIndependent_of_hasLeadingTerm` (Lib/GLn/SchurModule/MinorBasis.lean).

*Proof.* Take a nontrivial relation $\sum a_{\gamma, i} p_{\gamma, i} = 0$. Let $\gamma_0$ be the largest $\gamma$ in the column order with some $a_{\gamma, i} \ne 0$. The coefficient of $x_y^{\gamma_0}$ in the relation is $\sum_i a_{\gamma_0, i} q_{\gamma_0, i}$, since the terms with smaller $\gamma$ have no monomial at $\gamma_0$. So this sum is $0$, and the independence of $q_{\gamma_0, \cdot}$ gives $a_{\gamma_0, i} = 0$ for all $i$. This contradicts the choice of $\gamma_0$. $\square$

**Lemma.** Let $l$ be a weight, and for each $\gamma \in \operatorname{Int}(l(c(y), \cdot))$ let $l'_\gamma$ be a weight with $l = \gamma + l'_\gamma$. Let $p_{\gamma, i} \in \nabla(l)$ have leading terms $q_{\gamma, i} \cdot x_y^\gamma$, and let $\nabla(l'_\gamma)$ in the rows other than $y$ lie in the span of the $q_{\gamma, i}$. Then $\nabla(l)$ lies in the span of the $p_{\gamma, i}$.

Lean: `New.GL.nabla_le_span_of_hasLeadingTerm` (Lib/GLn/SchurModule/MinorBasis.lean).

*Proof.* Induction on the leading exponent of $f \in \nabla(l)$ in the column order, which is a monomial order and so a well order. If $f = 0$ there is nothing to prove. Otherwise let $\gamma$ be its leading exponent and $G$ its leading coefficient. By the first lemma of the previous subsection, $\gamma \in \operatorname{Int}(l(c(y), \cdot))$. By the second, $G \in \nabla(l'_\gamma)$. So $G = \sum_i a_i q_{\gamma, i}$. Then $f - \sum_i a_i p_{\gamma, i}$ lies in $\nabla(l)$ and has a smaller leading exponent. $\square$

*Proof of the standard basis theorem.* Induction on the number of rows. With no rows the claim is clear (`New.GL.exists_isStdMinorFamily_of_isEmpty`). Otherwise fix a row $y$. For each $\gamma \in \operatorname{Int}(l(c(y), \cdot))$, take the heights $k_\gamma$ of bordering, a family $I_{\gamma, \cdot}$ for the other rows by induction, and its lift $K_{\gamma, i}$. Properties 1 and 2 follow from the two lemmas above, and property 3 from the branching rule for alternants below. $\square$

**Lemma (branching rule for alternants).** Let $l$ be antitone, let $x \in \mathbb C^{N + 1}$ and let $i$ be an index. Let $x'$ be $x$ with the entry $i$ removed. Then

$$a_l(x) = (-1)^i \prod_{a \ne i} (x_a - x_i) \sum_{\gamma \in \operatorname{Int}(l)} x_i^{|\gamma|}\, a_{l - \gamma}(x').$$

Lean: `New.GL.alternant_succ` (Lib/GLn/SchurModule/MinorBasis.lean).

*Proof.* Column operations on $(x_a^{p_j})$ make the row $i$ equal to $(x_i^{p_0}, 0, \dots, 0)$ and put a factor $x_a - x_i$ in every other row (`Matrix.det_pow_eq_det_sub_mul_geom_sum`). Expand along the row $i$. The rest is a sum over $k_j \in [p_j, p_{j+1})$ of alternants in $x'$, and the choices of $k_j$ correspond to the $\gamma \in \operatorname{Int}(l)$. $\square$
Dividing by the case $l = 0$, where $\operatorname{Int}(0) = \{0\}$, gives the familiar form $s_l(x) = \sum_{\mu} x_i^{|l| - |\mu|} s_\mu(x')$ over the partitions $\mu$ that interlace $l$. It is the character form of the branching rule of Section 7.

### The chosen basis

The source turns the existence theorem into a fixed basis. For one place, rows $m$, heights below $N$ and $k(h)$ columns of height $h$, a set $s$ of fillings is a *standard set* if two things hold. (a) Over every commutative ring the minor products of $s$ are linearly independent, and the minor product of every filling lies in their span. (b) For every enumeration $e$ of the rows and every $x : m \to \mathbb C$, $\big(\sum_{T \in s} x^T\big) a_0(x \circ e) = a_\lambda(x \circ e)$, with $\lambda(i) = \sum_{i < h < N} k(h)$.

Lean: `New.IsTableauBasis` (Lib/GLn/SchurModule/Basic.lean).

**Lemma.** For a finite set of rows, a standard set exists, and the set chosen by `Classical.epsilon` is a standard set.

Lean: `New.exists_isTableauBasis`, `New.isTableauBasis_epsilon` (Lib/GLn/SchurModule/SchurMatrix.lean).

*Proof.* Apply the standard basis theorem with one colour, to the columns of the diagram. The span of all minor products contains the semi-invariants, and every minor product is a semi-invariant (Section 2), so the span of the family is the span of all minor products. The second statement is the specification of `Classical.epsilon`. $\square$

**Definition.** The *standard fillings* with rows $m$ are the members of the set chosen by `Classical.epsilon`. A *Weyl index* is a family that chooses a standard filling with rows $n_\tau$, heights below $|n_\tau|$ and multiplicities $\kappa_\tau$, for each place $\tau$. The *basis polynomial* $b_i$ of a Weyl index $i$ is the product over $\tau$ of the minor products of $i_\tau$ in the rows of the block $\tau$.

Lean: `New.BasisTableau`, `New.WeylIndexFamily` (Lib/GLn/SchurModule/Basic.lean), `New.nablaBasis` (Lib/GLn/SchurModule/Basic.lean).

**Remark (Formalization).** The set behind `New.BasisTableau` is chosen by `Classical.epsilon`. Only the properties of `New.IsTableauBasis` are known about it, and its members need not be semistandard tableaux (finding F-051 of the notes). No statement of the source refers to a particular basis element. The evaluation vectors and the polynomials $\sum \xi_i b_i$ change only by a change of basis under another choice.

**Theorem.** Over every commutative ring $R$, the basis polynomials $b_i$ are linearly independent, and the map $\xi \mapsto \sum_i \xi_i b_i$ has image exactly the module of semi-invariants of weight $\kappa$.

Lean: `New.linearIndependent_nablaBasis`, `New.range_nablaCombination` (Lib/GLn/SchurModule/SchurMatrix.lean). The map is `New.GL.nablaCombination` (Lib/GLn/SchurModule/Basic.lean).

*Proof.* Independence is an induction on the number of places: products of independent families in disjoint sets of variables are independent. The image is in $\nabla$ by Section 2. For the converse, the source proves a stronger statement with a power of the determinant, `New.nabla_le_span_nablaBasis_mul_detPow`, and takes the exponent $0$. $\square$

So the module of semi-invariants is free over every ring, with the basis $b_i$. The Weyl module of the source is the space of coordinate vectors $\xi$.
