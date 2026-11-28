---
title: Integral matrices and congruence subgroups
lean:
  - Lib/General/Groups/CongruenceSubgroups.lean
  - Lib/General/Groups/IndexOfProduct.lean
  - Lib/General/Groups/BesselGroups.lean
decls:
  - New.mem_intGL
  - New.intGL.map
  - New.intGL.map_eq_one
  - New.congruenceGL
  - New.Seesaw.index_pi_univ
  - New.parabolic
  - New.unitriangular
  - New.levi
  - New.parahoric
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Integral matrices and congruence subgroups

This section defines the congruence subgroups of $\mathrm{GL}_n$ that the source uses, and the block triangular subgroups that sit between them. The setting is a commutative ring $R$ with a subring $O$. The model is $R = \mathbb{Q}_p$ and $O = \mathbb{Z}_p$, or $R$ the finite adeles and $O$ the product of the local rings of integers. The source works with a subring of a fixed ring from the start. It does not form $\mathrm{GL}_n(O)$ as an abstract group. It forms the subgroup of $\mathrm{GL}_n(R)$ of matrices that are integral with their inverses. This keeps all the groups of the argument inside one ambient group, so that products and intersections make sense.

### Integral matrices

Let $n$ be a finite index set. The group $\mathrm{GL}_n(O)$ is [defined](/decl/New.intGL/) as the image of the map $\mathrm{GL}_n(O) \to \mathrm{GL}_n(R)$. The first lemma says that this image is what one expects.

**Lemma.** Let $O$ be a subring of a commutative ring $R$, and let $g \in \mathrm{GL}_n(R)$. Then $g \in \mathrm{GL}_n(O)$ if and only if every entry of $g$ and every entry of $g^{-1}$ lies in $O$.

Lean: `New.mem_intGL` (Lib/General/Groups/CongruenceSubgroups.lean).

*Proof.* If $g$ is the image of an invertible matrix over $O$, then $g^{-1}$ is the image of its inverse, so both have entries in $O$. Conversely, let $A$ and $B$ be the matrices over $O$ with the entries of $g$ and of $g^{-1}$. The map $O \to R$ is injective and multiplicative on matrices, and $AB$ maps to $g g^{-1} = 1$. So $AB = 1$ over $O$. A square matrix over a commutative ring with a right inverse is invertible. So $A \in \mathrm{GL}_n(O)$, and its image is $g$. $\square$

The condition on $g^{-1}$ cannot be dropped. Over $R = \mathbb{Q}_p$ and $O = \mathbb{Z}_p$, the matrix $\mathrm{diag}(p, 1)$ has entries in $\mathbb{Z}_p$, but its inverse does not. Equivalently, $g$ with entries in $O$ lies in $\mathrm{GL}_n(O)$ if and only if $\det g$ is a unit of $O$.

A ring map $f : O \to S$ acts on integral matrices entry by entry.

**Definition (Reduction of integral matrices).** Let $f : O \to S$ be a homomorphism of commutative rings. The *reduction* along $f$ is the homomorphism $\mathrm{GL}_n(O) \to \mathrm{GL}_n(S)$, $k \mapsto (f(k_{ij}))_{i,j}$. Here $k_{ij}$ is the entry of $k$, read as an element of $O$.

Lean: `New.intGL.map` (Lib/General/Groups/CongruenceSubgroups.lean). The matrix over $O$ is `New.intGL.toMatrix`, and the formula for the entries is `New.intGL.map_apply`.

**Lemma.** Let $f : O \to S$ be a ring homomorphism and let $k \in \mathrm{GL}_n(O)$. The reduction of $k$ along $f$ is $1$ if and only if $f(k_{ij} - \delta_{ij}) = 0$ for all $i, j$.

Lean: `New.intGL.map_eq_one` (Lib/General/Groups/CongruenceSubgroups.lean).

*Proof.* The reduction of $1$ is $1$. Two invertible matrices are equal if their entries are equal, and $f(k_{ij}) = f(\delta_{ij})$ is $f(k_{ij} - \delta_{ij}) = 0$. $\square$

So the kernel of the reduction along $O \to O/I$, for an ideal $I$ of $O$, is the set of $k$ with $k \equiv 1 \pmod I$. This is the principal congruence subgroup of level $I$. The source defines a more general family directly, by conditions on rows.

### Congruence subgroups

**Definition (Congruence subgroup).** Let $O$ be a subring of $R$, let $M$ be an $O$-submodule of $R$, let $m$ be an index set and let $e : m \to n$ be a map. The *congruence subgroup* $\Gamma(M, e)$ is the set of $g \in \mathrm{GL}_n(O)$ such that, for every $i \in m$ and every $j \in n$, the entry of $g - 1$ in row $e(i)$ and column $j$ lies in $M$.

Lean: `New.congruenceGL` (Lib/General/Groups/CongruenceSubgroups.lean).

The set $\Gamma(M, e)$ is a subgroup. It contains $1$. Let $g, k \in \Gamma(M, e)$. Then $g k^{-1} \in \mathrm{GL}_n(O)$, and
$$g k^{-1} - 1 = \big((g - 1) - (k - 1)\big) k^{-1}.$$
Row $e(i)$ of $(g - 1) - (k - 1)$ has entries in $M$, and $k^{-1}$ has entries in $O$. Since $M$ is an $O$-module, row $e(i)$ of the product has entries in $M$. So $g k^{-1} \in \Gamma(M, e)$.

Two cases matter. If $m = n$ and $e$ is the identity, every row is constrained, and $\Gamma(M, e)$ is the set of $g \in \mathrm{GL}_n(O)$ with $g \equiv 1$ modulo $M$. For $M$ an ideal of $O$ this is the principal congruence subgroup $\Gamma(M)$. If $e$ picks out a subset of the rows, the other rows of $g$ are free.

**Example (The group $\Gamma_1(N)$).** Let $R = \mathbb{Q}$, $O = \mathbb{Z}$, $n = \{1, 2\}$ and $M = N\mathbb{Z}$. Let $m$ have one element, and let $e$ pick the second row. Then $\Gamma(M, e)$ is the set of $\begin{pmatrix} a & b \\ c & d \end{pmatrix} \in \mathrm{GL}_2(\mathbb{Z})$ with $c \equiv 0$ and $d \equiv 1 \pmod N$. Its intersection with $\mathrm{SL}_2(\mathbb{Z})$ is the classical group $\Gamma_1(N)$ (Diamond and Shurman, *A First Course in Modular Forms*, Definition 1.2.1). If $e$ picks both rows, the intersection with $\mathrm{SL}_2(\mathbb{Z})$ is $\Gamma(N)$.

The source uses these groups for the level structures of the lattices in Theorem A and in the gluing of levels in the seesaw identity. The group $\Gamma(M, e)$ with $e$ the last row is the congruence form of the mirabolic subgroup, the stabiliser of the last basis covector. In a $p$-adic group it is the group that fixes a vector of a lattice modulo $M$.

### Indices of products

Adelic subgroups are products of local subgroups, and their indices are products of local indices. The source proves the general form.

**Lemma.** Let $I$ be a finite set, let $G_i$ be groups and let $H_i \leq G_i$ be subgroups. Then
$$\Big[\prod_{i \in I} G_i : \prod_{i \in I} H_i\Big] = \prod_{i \in I} [G_i : H_i].$$

Lean: `New.Seesaw.index_pi_univ` (Lib/General/Groups/IndexOfProduct.lean).

*Proof.* The cosets of $\prod_i H_i$ are the families of cosets of the $H_i$: the map $(g_i H_i)_i \mapsto (g_i)_i \prod_i H_i$ is a bijection $\prod_i G_i/H_i \to \prod_i G_i / \prod_i H_i$. The cardinality of a finite product of sets is the product of the cardinalities. $\square$

**Remark (Formalization).** The index of a subgroup of infinite index is read as $0$. With this reading the lemma holds without any finiteness condition on the indices: if some $[G_i : H_i]$ is infinite, both sides are $0$. The same convention applies to the cardinality of an infinite set, which is read as $0$. So a statement of the source of the form "the index is $N$" with $N \neq 0$ also says that the index is finite. Mathlib's `Subgroup.index_pi` (Mathlib) is the case where all the $G_i$ are equal.

### Special matrices

The source names three kinds of elementary matrices. For a family $t = (t_i)$ of units of $R$, the diagonal matrix $\mathrm{diag}(t)$ is a homomorphism $(R^\times)^n \to \mathrm{GL}_n(R)$. For $i \neq j$ and $a \in R$, the transvection $1 + a E_{ij}$ is invertible with inverse $1 - a E_{ij}$. The transpose $g \mapsto g^t$ is an anti-homomorphism, and $g \mapsto (g^t)^{-1}$ is a homomorphism.

Lean: `New.diagGL`, `New.transvectionGL`, `New.transposeGL` (Lib/General/Groups/CongruenceSubgroups.lean).

### Block triangular subgroups

The groups at the real place of Theorem B, and the parahoric groups at the finite places, are block triangular. The source describes a block structure by a *level function* $\ell : n \to \Lambda$ into a linearly ordered set. Two indices with the same level lie in the same block.

**Definition (Parabolic and unipotent subgroups).** Let $\ell : n \to \Lambda$ be a level function.

1. The *parabolic subgroup* $P_\ell$ is the group of $g \in \mathrm{GL}_n(R)$ with $g_{ij} = 0$ whenever $\ell(j) < \ell(i)$. These are the block upper triangular matrices.
2. The *unipotent subgroup* $N_\ell$ is the group of $g \in \mathrm{GL}_n(R)$ with $g_{ij} = \delta_{ij}$ whenever $\ell(j) \leq \ell(i)$. These are the block upper triangular matrices whose diagonal blocks are identity matrices.

Lean: `New.parabolic`, `New.unitriangular` (Lib/General/Groups/BesselGroups.lean).

The set $P_\ell$ is closed under products and inverses because a product of block upper triangular matrices is block upper triangular, and so is the inverse. For $N_\ell$ the source proves a general criterion. Let $r$ be a relation on $n$ such that $r(i, j)$ implies $r(i, k)$ or $r(k, j)$ for every $k$. Then the set of invertible $g$ with $g_{ij} = \delta_{ij}$ whenever $r(i, j)$ is a subgroup (`New.agreeWithOneOn`). The relation $\ell(j) \leq \ell(i)$ has the property, since $\ell(k) \leq \ell(i)$ or $\ell(j) \leq \ell(k)$ by linearity. The group $N_\ell$ is normal (`New.conj_mem_unitriangular`) in $P_\ell$, and its elements have determinant $1$ (`New.det_eq_one_of_unitriangular`). The map $P_\ell \to \mathrm{GL}$ that takes a matrix to its diagonal block of a given level is [a homomorphism](/decl/New.blockHom/).

**Definition (Levi and parahoric subgroups).** Let $W$ be a commutative local ring with maximal ideal $\mathfrak{m}$, let $k \geq 1$, and let $\tau : \{1, \dots, k\} \to \mathbb{N}$ be a labelling of the indices.

1. The *Levi subgroup* $L_\tau$ is the group of $g \in \mathrm{GL}_k(W)$ with $g_{ij} = 0$ whenever $\tau(i) \neq \tau(j)$.
2. The *parahoric subgroup* $P^\circ_\tau$ is the group of $g \in \mathrm{GL}_k(W)$ with $g_{ij} \in \mathfrak{m}$ whenever $\tau(i) < \tau(j)$.

Lean: `New.levi`, `New.parahoric` (Lib/General/Groups/BesselGroups.lean).

The parahoric subgroup is the preimage of a parabolic subgroup under the reduction $\mathrm{GL}_k(W) \to \mathrm{GL}_k(W/\mathfrak{m})$. The parabolic subgroup is the one for the level function $\tau$ with the order reversed, so that its matrices are block lower triangular. For $W = \mathbb{Z}_p$ and $\tau$ injective, $P^\circ_\tau$ is an Iwahori subgroup of $\mathrm{GL}_k(\mathbb{Z}_p)$. For $\tau$ constant, it is all of $\mathrm{GL}_k(\mathbb{Z}_p)$. The Levi subgroup $L_\tau$ is the group of block diagonal matrices, a product of smaller general linear groups.

**Remark (Formalization).** The Levi subgroup is defined as the group of matrices that agree with the identity at the entries with $\tau(i) \neq \tau(j)$, through the criterion above. The relation $\tau(i) \neq \tau(j)$ has the property of the criterion. The definition carries the hypothesis that $W$ is local, and it does not use it. The parahoric subgroup does use it, through the residue field. A hypothesis that is not used makes the definition apply to fewer rings. It does not change the group where the definition applies.
