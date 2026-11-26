---
title: Labels and the good idempotent
lean:
  - New/UpperBound/Objects/LabelsAndIndexTypes.lean
decls:
  - New.IsPrimitivePolynomial
  - New.IsPrimitivePolynomial.scaleRoots
  - New.IsPrimitivePolynomial.pow_geom_sum_eq_prod_aroots
  - New.IsPrimitivePolynomial.isPrimitiveRoot_prod_aroots
  - New.IsAllowedPolynomial
  - New.goodTuples
  - New.mem_goodTuples
  - New.Data.chosenGL
  - New.Data.goodTupleFamilies
  - New.Data.mem_goodTupleFamilies
  - New.Data.e₀
  - New.Data.isCentralProj_e₀
  - New.Data.hyperplaneSum_mul_e₀
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Labels and the good idempotent

Theorem A does not count all forms on $Y_0$. It counts the *good* forms: the forms on which a finite group $\bar G$ acts through a fixed set of its irreducible representations. The set is cut out by a central idempotent $e_0$ of the group algebra $\mathbb{C}[\bar G]$. The choice of $e_0$ has one purpose. In the unfolding of the seesaw identity, some terms carry a local factor of a special shape, a *hyperplane sum*. The idempotent $e_0$ must kill every such term. The last lemma of this section says that it does.

### Model case: one place, rank one

Take $r = 1$ and one finite field $k = \mathbb{F}_7$. Then $\mathrm{GL}_1(k) = k^\times$ is cyclic of order $6$. Its irreducible representations are the six characters, and a *label* of degree $1$ is a polynomial $X - \alpha$ with $\alpha \neq 0$. The label $X - \alpha$ names the character that corresponds to $\alpha$ under a fixed isomorphism of the character group with $k^\times$. In rank $1$ every invertible $1 \times 1$ matrix fixes the hyperplane $\{0\}$, so the hyperplane sum for a character $\chi$ is $\sum_{h \in k^\times} \chi(h)^{-1} h$. Its product with the idempotent of the character named by $\alpha$ is zero unless that character is $\chi$. So to kill the hyperplane sums for all characters $\chi$ with $\chi^M = 1$, the idempotent must avoid the labels $\alpha$ with $\alpha^M = 1$.

Take $M = 2$. The labels with $\alpha^2 \neq 1$ are $\alpha \in \{2, 3, 4, 5\}$. These are the *allowed* labels. Among them, $3$ and $5$ generate $k^\times$; these are the *primitive* labels. With one place, a good tuple is one allowed label that is also primitive, so the good labels are $X - 3$ and $X - 5$. The good idempotent is the sum of the two idempotents of the characters named by $3$ and $5$.

### Labels, primitive and allowed polynomials

Let $k$ be a finite field with $q$ elements. A label of degree $r$ over $k$ (`New.IsLabel`, from [characters of GL_n over a finite field](/chapter/finite-gln/)) is a monic squarefree polynomial $c \in k[X]$ of degree $r$ with $c(0) \neq 0$. To each label $c$ the background attaches an irreducible character $\Xi_c$ of $\mathrm{GL}_r(k)$ and its central idempotent $e_c$ ([labelIdem](/decl/New.labelIdem/)). For a tuple $c = (c_w)$ over fields $k_w$, the idempotent $e_c = \bigotimes_w e_{c_w}$ in $\mathbb{C}[\prod_w \mathrm{GL}_r(k_w)]$ is [tupleIdem](/decl/New.tupleIdem/).

**Definition (Primitive polynomial).** A polynomial $c \in k[X]$ is *primitive of degree $r$* if it is a label of degree $r$, it is irreducible, and it has a root $\xi$ in an algebraic closure of $k$ of multiplicative order exactly $q^r - 1$.

Lean: `New.IsPrimitivePolynomial` (New/UpperBound/Objects/LabelsAndIndexTypes.lean).

So $\xi$ generates the units of the field with $q^r$ elements, and $c$ is its minimal polynomial.

**Lemma.** Let $c$ be primitive of degree $r$ over $k$, let $a \in k^\times$ with $a^M = 1$, and suppose that $M^2$ divides $q - 1$. Then the polynomial $c^{(a)}$ whose roots are the roots of $c$ times $a$ (`Polynomial.scaleRoots`) is primitive of degree $r$.

Lean: `New.IsPrimitivePolynomial.scaleRoots` (New/UpperBound/Objects/LabelsAndIndexTypes.lean).

*Proof.* Scaling the roots by a unit keeps $c$ monic, squarefree, of degree $r$, with nonzero constant term, and irreducible. The element $a\xi$ is a root of $c^{(a)}$. It remains to see that $a\xi$ has order $q^r - 1$. Let $o$ be the order of $a$. For a prime $p$ that divides $o$, we have $p\,o \mid o^2 \mid M^2 \mid q - 1 \mid q^r - 1 = \mathrm{ord}(\xi)$. For commuting elements $u, v$ of finite order, if $p \cdot \mathrm{ord}(u)$ divides $\mathrm{ord}(v)$ for every prime $p \mid \mathrm{ord}(u)$, then $\mathrm{ord}(uv) = \mathrm{ord}(v)$. Apply this with $u = a$ and $v = \xi$. $\square$

The hypothesis $M^2 \mid q - 1$ is needed. In the model case $q = 7$ and $M = 2$, so $M^2 = 4$ does not divide $6$. Scaling the primitive label $X - 3$ by $a = -1$ gives $X - 4$, and $4$ has order $3$.

**Lemma.** Let $c$ be primitive of degree $r$ over $k$, and let $\xi$ be a root of $c$. Then $\xi^{1 + q + \dots + q^{r-1}}$ is the product of the roots of $c$, and this product is a primitive $(q-1)$-th root of unity.

Lean: `New.IsPrimitivePolynomial.pow_geom_sum_eq_prod_aroots` (New/UpperBound/Objects/LabelsAndIndexTypes.lean).

Lean: `New.IsPrimitivePolynomial.isPrimitiveRoot_prod_aroots` (New/UpperBound/Objects/LabelsAndIndexTypes.lean).

*Proof.* As $c$ is irreducible, its roots are the Frobenius conjugates $\xi^{q^i}$ for $i < r$. Their product is $\xi^e$ with $e = \sum_{i<r} q^i$. As $e(q - 1) = q^r - 1$ and $\xi$ has order $q^r - 1$, the power $\xi^e$ has order $q - 1$. $\square$

The product of the roots is the norm of $\xi$ to $k$, so the lemma says that the norm of a generator is a generator. For example, over $\mathbb{F}_3$ the polynomial $X^2 + X + 2$ is primitive. Its roots have product $2$, which has order $2 = q - 1$.

**Definition (Allowed polynomial).** A polynomial $c \in k[X]$ is *allowed* for $M$ and $r$ if it is a label of degree $r$ and no $x \in k$ with $x^M = 1$ is a root of $c$.

Lean: `New.IsAllowedPolynomial` (New/UpperBound/Objects/LabelsAndIndexTypes.lean).

**Definition (Good tuple).** Let $(k_w)_{w \in I}$ be a finite family of finite fields. A tuple $(c_w)$ with $c_w \in k_w[X]$ is *good* for $M$ and $r$ if every $c_w$ is allowed for $M$ and $r$, and at least one $c_w$ is primitive of degree $r$.

Lean: `New.goodTuples` (New/UpperBound/Objects/LabelsAndIndexTypes.lean).

Lean: `New.mem_goodTuples` (New/UpperBound/Objects/LabelsAndIndexTypes.lean).

The Lean definition is a finset: the tuples of monic polynomials of degree $r$ with the two properties. The lemma `New.mem_goodTuples` removes the condition on the degree, as an allowed polynomial is a label and so is monic of degree $r$.

### The group and the idempotent

The data $D$ fix two level primes $p_0, p_1$ and the element $\pi_M$ of the ring of integers of $E$. A *chosen place* above $p_i$ is a finite place $w$ of $E$ that divides both $p_i$ and $\pi_M$. There are finitely many. Let $\mathbb{F}_w$ be the residue field at $w$. The rows of the target are indexed by a set `D.RowIndex` with $r$ elements ([card_rowIndex](/decl/New.Data.card_rowIndex/)).

**Definition (The finite group).** The group $\bar G$ is the product of the groups $\mathrm{GL}_r(\mathbb{F}_w)$ over the pairs $(i, w)$ with $w$ a chosen place above $p_i$.

Lean: `New.Data.chosenGL` (New/UpperBound/Objects/LabelsAndIndexTypes.lean).

Put $q_2 = (q_0 d)^{s+6}$, with $q_0$ and $d$ parameters of $P$ and $s$ the tower exponent of $D$ (`New.Parameters.q₂`).

**Definition (Good families and the good idempotent).** A family $c = (c_w)$, with $c_w \in \mathbb{F}_w[X]$ for each chosen place $w$, is a *good family* if, for $i = 0$ and for $i = 1$, the tuple of the $c_w$ with $w$ above $p_i$ is good for $q_2$ and $r$. The *good idempotent* is
$$e_0 = \sum_{c \text{ good}} e_c \in \mathbb{C}[\bar G].$$

Lean: `New.Data.goodTupleFamilies` (New/UpperBound/Objects/LabelsAndIndexTypes.lean).

Lean: `New.Data.mem_goodTupleFamilies` (New/UpperBound/Objects/LabelsAndIndexTypes.lean).

Lean: `New.Data.e₀` (New/UpperBound/Objects/LabelsAndIndexTypes.lean).

So a good family has a primitive label above $p_0$ and a primitive label above $p_1$. No label at any chosen place has a $q_2$-th root of unity of $\mathbb{F}_w$ as a root.

**Proposition.** The element $e_0$ is a central idempotent: $e_0^2 = e_0$, and its coefficient function is a class function on $\bar G$.

Lean: `New.Data.isCentralProj_e₀` (New/UpperBound/Objects/LabelsAndIndexTypes.lean).

*Proof.* This is [isCentralProj_sum_tupleIdem](/decl/New.isCentralProj_sum_tupleIdem/) for the finset of good families: the $e_c$ are central idempotents, distinct tuples give orthogonal ones, and a sum of orthogonal idempotents is an idempotent. A sum of class functions is a class function. $\square$

### The idempotent kills hyperplane sums

For a character $\chi$ of $\mathbb{F}_w^\times$ and a nonzero vector $l \in \mathbb{F}_w^r$, the hyperplane sum is
$$H_{\chi, l} = \sum_h \chi(\det h)^{-1}\, h \in \mathbb{C}[\mathrm{GL}_r(\mathbb{F}_w)],$$
where $h$ runs over the invertible matrices $1 + u\,l^{\mathsf T}$, $u \in \mathbb{F}_w^r$. These are the matrices that fix the hyperplane $l \cdot x = 0$ pointwise. The background result is: $H_{\chi, l}\, e_c = 0$ whenever the name of $\chi$, a unit of $\mathbb{F}_w$, is not a root of $c$ ([hyperplaneSum_mul_labelIdem](/decl/New.hyperplaneSum_mul_labelIdem/)).

**Lemma.** Let $(x_v)$ be a family with $x_v \in \mathbb{C}[\mathrm{GL}_r(\mathbb{F}_v)]$ for each chosen place $v$. Suppose that at one chosen place $v$ we have $x_v = H_{\chi, l}$ with $l \neq 0$ and $\chi^{q_2} = 1$. Then $\left(\bigotimes_v x_v\right) e_0 = 0$.

Lean: `New.Data.hyperplaneSum_mul_e₀` (New/UpperBound/Objects/LabelsAndIndexTypes.lean).

*Proof.* Expand $e_0$ as the sum of the $e_c$ over the good families $c$. It is enough to show that each product $(\bigotimes x_v)\, e_c$ is zero. As $e_c = \bigotimes e_{c_v}$, the product is the tensor of the products $x_v e_{c_v}$, and it is enough that the factor at $v$ is zero. As $\chi^{q_2} = 1$, the name of $\chi$ is a $q_2$-th root of unity in $\mathbb{F}_v$. As $c$ is good, $c_v$ is allowed for $q_2$, so the name of $\chi$ is not a root of $c_v$. The background result gives $H_{\chi, l}\, e_{c_v} = 0$. $\square$

This is the reason for the allowed condition. The primitive condition plays no part here. It is used later, in the count of good forms and in the size of the good part ([Theorem A and its plan](/chapter/theorem-a-plan/)).

**Remark (Formalization).** Three points.

1. The file makes `Fintype.ofFinite` a local instance of low priority. The finsets `New.goodTuples` and `New.Data.goodTupleFamilies` use classical decidability. Neither changes the mathematics.
2. The rank in `New.Data.goodTupleFamilies` is written `card D.RowIndex`, not $r$. These are equal by [card_rowIndex](/decl/New.Data.card_rowIndex/).
3. Nothing in this file proves $e_0 \neq 0$. If $e_0 = 0$, then the space of good forms is $0$, and Theorem A says nothing. The source proves later that the target forms, the good forms on $Y_0$, are nonzero ([the target is nonzero](/decl/New.Data.finrank_targetForms_ne_zero/)), and so $e_0 \neq 0$. A direct argument, not in the source, also exists. There are $f \ge 1$ chosen places above each $p_i$ (`New.Data.card_chosenPlace`). As $r \ge 2$, a primitive polynomial is irreducible of degree at least $2$, so it has no root in its base field and it is allowed. The minimal polynomial of a generator of $\mathbb{F}_{q^r}^\times$ is primitive. So the family of such polynomials at every chosen place is good. For a label $c$, the character $\Xi_c$ is irreducible (`New.IsLabel.isIrreducibleChar_labelChar`), so $e_c \neq 0$. A tensor of nonzero idempotents is nonzero, and a sum of orthogonal nonzero idempotents is nonzero.
