---
title: Characters of profinite groups
lean:
  - Lib/General/Groups/ProfiniteCharacters.lean
decls:
  - New.QZ.exists_extend
  - New.QZ.eq_zero_of_forall_hom_eq_zero
  - New.QZ.bijective_ofZMod_comp
  - New.card_hom_QZ
  - New.QZChar.exists_apply_ne_zero_of_notMem_ker
  - New.QZChar.isOfFinAddOrder_of_compactSpace
  - New.QZChar.exists_eval_eq
  - New.QZChar.mem_of_forall_abelianLift
  - New.QZChar.abelianization_ext
  - New.QZChar.exists_hom_abelianLift_eq
  - New.QZChar.continuous_iff_forall_isOpen_ker_comp
  - New.exists_monoidHom_extend
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Characters of profinite groups

Class field theory describes the abelianisation of a Galois group. To compare two such descriptions, one tests elements against characters. This section gives the duality facts that make this test valid. The group of values is $\mathbb{Q}/\mathbb{Z}$ with the discrete topology. The groups are profinite. The facts are the classical ones: a divisible group is injective, a finite abelian group and its dual have the same order, and the characters of a profinite group separate the points of its abelianisation. The users are the Artin maps of [the class field theory chapter](/chapter/class-field-theory/), the Grunwald theorem and the Hecke characters.

### The group of values

Let $\mathbb{Q}/\mathbb{Z}$ have the discrete topology. For a topological group $G$, a character of $G$ is a continuous homomorphism $\chi : G \to \mathbb{Q}/\mathbb{Z}$. The characters make a group under pointwise addition. In this section we write $X(G)$ for this group. Since the target is discrete, a homomorphism is continuous exactly when its kernel is open.

The source defines $X(G)$ as the group of continuous $1$-cocycles of $G$ with values in $\mathbb{Q}/\mathbb{Z}$ for the trivial action. For the trivial action, the cocycle condition is $\chi(gh) = \chi(g) + \chi(h)$, so the two definitions agree. The map $x \mapsto e^{2\pi i x}$ identifies $\mathbb{Q}/\mathbb{Z}$ with the roots of unity in $\mathbb{C}^\times$. The source has this map as `New.QZ.expUnit` and proves that its kernel is trivial.

The first fact is the injectivity of a divisible group, in a form that does not ask the map to be injective.

**Lemma.** Let $A$, $B$ and $W$ be abelian groups with $W$ divisible. Let $f : A \to B$ and $u : A \to W$ be homomorphisms with $\ker f \subseteq \ker u$. Then there is a homomorphism $v : B \to W$ with $v \circ f = u$.

Lean: `New.QZ.exists_extend` (Lib/General/Groups/ProfiniteCharacters.lean).

*Proof.* The map $u$ factors through $A/\ker f$, and $f$ induces an injection $A/\ker f \to B$. A divisible abelian group is an injective $\mathbb{Z}$-module (Weibel, *An Introduction to Homological Algebra*, §2.3, from Baer's criterion). So the induced map on $A/\ker f$ extends to $B$. $\square$

**Corollary.** Let $a$ be an element of an abelian group $A$. If $u(a) = 0$ for every homomorphism $u : A \to \mathbb{Q}/\mathbb{Z}$, then $a = 0$.

Lean: `New.QZ.eq_zero_of_forall_hom_eq_zero` (Lib/General/Groups/ProfiniteCharacters.lean).

*Proof.* If $a \neq 0$, the cyclic group $\langle a \rangle$ has a nonzero homomorphism to $\mathbb{Q}/\mathbb{Z}$ that is nonzero at $a$. Extend it to $A$ by the lemma. $\square$

The second fact is a count. Let $n \geq 1$. The map $k \mapsto k/n$ embeds $\mathbb{Z}/n$ in $\mathbb{Q}/\mathbb{Z}$, and its image is the set of elements killed by $n$.

**Lemma.** Let $n \geq 1$ and let $A$ be an abelian group with $na = 0$ for all $a \in A$. Then composition with the embedding $\mathbb{Z}/n \to \mathbb{Q}/\mathbb{Z}$ is a bijection from $\mathrm{Hom}(A, \mathbb{Z}/n)$ to $\mathrm{Hom}(A, \mathbb{Q}/\mathbb{Z})$.

Lean: `New.QZ.bijective_ofZMod_comp` (Lib/General/Groups/ProfiniteCharacters.lean).

*Proof.* The embedding is injective. Each value $u(a)$ is killed by $n$, so it lies in the image. $\square$

**Theorem.** Let $A$ be a finite abelian group. Then $|\mathrm{Hom}(A, \mathbb{Q}/\mathbb{Z})| = |A|$.

Lean: `New.card_hom_QZ` (Lib/General/Groups/ProfiniteCharacters.lean).

This is the order statement of duality for finite abelian groups (Serre, *A Course in Arithmetic*, Ch. VI, §1). The proof uses the structure theorem: $A$ is a product of cyclic groups, $\mathrm{Hom}$ turns finite products into products, and $\mathrm{Hom}(\mathbb{Z}/n, \mathbb{Q}/\mathbb{Z})$ has $n$ elements. The source uses the theorem in the Selmer counts and in the Greenberg and Wiles formula, where it turns the order of a dual group into the order of the group.

### Characters separate points

Let $G$ be a topological group. The group $G$ is nonarchimedean if every neighbourhood of $1$ contains an open subgroup. A profinite group has this property.

**Proposition.** Let $G$ be a nonarchimedean group, let $C$ be an abelian group and let $f : G \to C$ be a homomorphism with closed kernel. Let $\sigma \in G$ with $\sigma \notin \ker f$. Then there is a character $\chi$ of $G$ with $\chi = 0$ on $\ker f$ and $\chi(\sigma) \neq 0$.

Lean: `New.QZChar.exists_apply_ne_zero_of_notMem_ker` (Lib/General/Groups/ProfiniteCharacters.lean).

*Proof.* The complement of $\ker f$ is open and contains $\sigma$. So there is an open subgroup $V$ with $\sigma V \cap \ker f = \emptyset$. Then $f(\sigma) \notin f(V)$. By the corollary, a homomorphism $u : C/f(V) \to \mathbb{Q}/\mathbb{Z}$ is nonzero at the class of $f(\sigma)$. The composite $\chi = u \circ (C \to C/f(V)) \circ f$ kills $V$. So its kernel is open and $\chi$ is continuous. It kills $\ker f$, and $\chi(\sigma) \neq 0$. $\square$

From now on let $G$ be compact. A character has an open kernel of finite index, so it has finite order (`New.QZChar.isOfFinAddOrder_of_compactSpace`). The next theorem is the surjectivity half of duality: every homomorphism from the dual group to $\mathbb{Q}/\mathbb{Z}$ is evaluation at a point.

**Theorem.** Let $G$ be a compact group and let $t : X(G) \to \mathbb{Q}/\mathbb{Z}$ be a homomorphism. Then there is $g \in G$ with $\chi(g) = t(\chi)$ for every character $\chi$.

Lean: `New.QZChar.exists_eval_eq` (Lib/General/Groups/ProfiniteCharacters.lean).

*Proof.* For each $\chi$ the set $\{g : \chi(g) = t(\chi)\}$ is closed. Since $G$ is compact, it is enough to meet finitely many of these conditions at once. Let $S$ be a finite set of characters and let $T$ be the subgroup that $S$ generates. Each character has finite order, so $T$ is finite. Let $E$ be the group of homomorphisms $T \to \mathbb{Q}/\mathbb{Z}$ that are evaluation at a point of $G$. Points separate characters, so $T$ embeds in the dual of $E$. By the theorem on finite groups, $|\mathrm{Hom}(T, \mathbb{Q}/\mathbb{Z})| = |T| \leq |E|$. So $E$ is the full dual of $T$, and the restriction of $t$ to $T$ is evaluation at a point. $\square$

Let $G^{\mathrm{ab}}$ be the topological abelianisation, the quotient of $G$ by the closure of its commutator subgroup. Each character $\chi$ induces a homomorphism $\chi^{\mathrm{ab}} : G^{\mathrm{ab}} \to \mathbb{Q}/\mathbb{Z}$. For the rest of this section let $G$ be profinite, that is compact and totally disconnected.

**Theorem.** Let $G$ be profinite and let $H$ be a closed subgroup of $G^{\mathrm{ab}}$. Let $\sigma \in G^{\mathrm{ab}}$. If $\chi^{\mathrm{ab}}(\sigma) = 0$ for every character $\chi$ with $\chi^{\mathrm{ab}} = 0$ on $H$, then $\sigma \in H$.

Lean: `New.QZChar.mem_of_forall_abelianLift` (Lib/General/Groups/ProfiniteCharacters.lean).

*Proof.* Apply the proposition to the projection $G \to G^{\mathrm{ab}}/H$. Its kernel is closed because $H$ is closed. $\square$

**Corollary.** Let $G$ be profinite and let $g, g' \in G^{\mathrm{ab}}$. If $\chi^{\mathrm{ab}}(g) = \chi^{\mathrm{ab}}(g')$ for every character $\chi$, then $g = g'$.

Lean: `New.QZChar.abelianization_ext` (Lib/General/Groups/ProfiniteCharacters.lean).

*Proof.* Take $H = \{1\}$ and $\sigma = g g'^{-1}$ in the theorem. The trivial subgroup is closed because $G^{\mathrm{ab}}$ is Hausdorff. $\square$

These two results are the injectivity half of Pontryagin duality for profinite groups (Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, Ch. I, §1). The source needs only the parts below, which build homomorphisms into $G^{\mathrm{ab}}$ and test their continuity.

**Theorem.** Let $G$ be profinite and let $Y$ be a group. Let $s$ be a homomorphism from $Y$ to the homomorphisms $X(G) \to \mathbb{Q}/\mathbb{Z}$. Then there is a homomorphism $f : Y \to G^{\mathrm{ab}}$ with $\chi^{\mathrm{ab}}(f(y)) = s(y)(\chi)$ for every character $\chi$ and every $y \in Y$.

Lean: `New.QZChar.exists_hom_abelianLift_eq` (Lib/General/Groups/ProfiniteCharacters.lean).

*Proof.* For each $y$, the theorem on evaluation gives a point $g_y \in G$ with $\chi(g_y) = s(y)(\chi)$ for all $\chi$. Let $f(y)$ be the class of $g_y$. The classes of $g_{yz}$ and $g_y g_z$ have the same value under every $\chi^{\mathrm{ab}}$, so they are equal by the corollary. Thus $f$ is a homomorphism. $\square$

**Remark (Formalization).** The proof picks the point $g_y$ with `choose`. The point in $G$ is not unique, because two points with the same class in $G^{\mathrm{ab}}$ have the same character values. Only the class enters the statement, and the corollary shows that the class is unique. So the homomorphism $f$ does not depend on the choice. The Artin maps of the source are built from this theorem, so the same remark applies to them: the map is unique, but its definition goes through a choice.

**Proposition.** Let $G$ be profinite, let $C$ be an abelian topological group and let $f : C \to G^{\mathrm{ab}}$ be a homomorphism. Then $f$ is continuous if and only if $\chi^{\mathrm{ab}} \circ f$ has open kernel for every character $\chi$.

Lean: `New.QZChar.continuous_iff_forall_isOpen_ker_comp` (Lib/General/Groups/ProfiniteCharacters.lean).

*Proof.* The map $g \mapsto (\chi^{\mathrm{ab}}(g))_\chi$ is continuous and injective by the corollary. It goes from a compact space to a Hausdorff product of discrete groups, so it is a closed embedding. Thus $f$ is continuous if and only if each coordinate $\chi^{\mathrm{ab}} \circ f$ is continuous. A homomorphism to a discrete group is continuous exactly when its kernel is open. $\square$

### Extension of characters

The last result of the file is the multiplicative form of the first lemma. It is the step that extends a character from a subgroup in the constructions of Hecke characters and in the Grunwald theorem.

**Proposition.** Let $A$ and $G$ be abelian groups and let $C$ be a divisible abelian group. Let $f : A \to G$ and $\theta : A \to C$ be homomorphisms and let $H \leq G$ be a subgroup. Assume that $\theta(a) = 1$ for every $a$ with $f(a) \in H$. Then there is a homomorphism $\chi : G \to C$ with $H \subseteq \ker \chi$ and $\chi \circ f = \theta$.

Lean: `New.exists_monoidHom_extend` (Lib/General/Groups/ProfiniteCharacters.lean).

*Proof.* Apply the first lemma to the composite $A \to G \to G/H$ and to $\theta$. The hypothesis says that the kernel of the composite is in $\ker \theta$. Pull the extension back to $G$. $\square$

The proposition is purely algebraic. A user who wants a continuous character must check the continuity separately, for example with an open kernel.

**Remark (Formalization).** The file adds two global instances. The first, at line 199, declares the Mathlib fact `isClosed_topologicalClosure` an instance. It is about the closure of a subgroup, the subgroup by which the topological abelianisation is a quotient. The second, at line 309, says that a compact totally disconnected group is nonarchimedean. Both state true facts, and both apply in every file that imports this one. The second instance gives a structure on $G$ that Mathlib can also reach by other routes. The statement is a proposition, so two proofs of it are equal and no diamond can come from it. Row F-023 of [the register of findings](/chapter/register-of-findings/) lists global instances of other files, and not these two.
