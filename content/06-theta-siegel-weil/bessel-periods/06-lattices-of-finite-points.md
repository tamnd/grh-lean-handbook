---
title: Lattices of finite points
lean:
  - Lib/Weil/Periods/PointLattice.lean
  - Lib/Weil/Periods/LatticeBounds.lean
  - Lib/Weil/Periods/GradedLattice.lean
decls:
  - New.Space.lattice
  - New.Space.mem_lattice_iff_formFin
  - New.Space.lattice_le_iff
  - New.Space.lattice_eq_iff
  - New.Grading.IsGraded
  - New.Grading.latticeMinus
  - New.Grading.latticePlus
  - New.Grading.HasLatticeBounds
  - New.Grading.HasBoundedOrbit
  - New.Grading.mem_latticeMinus_iff_formFin
  - New.Grading.mem_latticePlus_iff_formFin
  - New.Grading.exists_lattice_inclXFin_mul_eq
  - New.Grading.finite_image_latticeMinus
  - New.Grading.HasLatticeBounds.latticeMinus_componentOn
  - New.Grading.exists_finite_representatives
  - New.Grading.exists_basis_hasDegreeGe
  - New.Grading.exists_gram_mul_eq_gram_degreeZeroPart
  - New.Grading.exists_isGraded
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Lattices of finite points

When the step of the last section is repeated, the finite part of the argument of $W'$ must stay in a controlled set. A finite point $x$ of the unitary group gives a self-dual lattice $\Lambda(x)$. The grading cuts $\Lambda(x)$ into two lattices in $X^{\perp}$, an intersection and a projection. The section proves three results. First, two points whose lattices have the same intersection with $X^{\perp}$ differ by a point of $U(X)$, up to the stabiliser of the standard lattice. Second, the points whose intersection satisfies given bounds fall into finitely many classes. Third, every point can be moved by a unipotent element to a point whose lattice is graded.

### The lattice of a point

Let $\hat{\mathcal{O}}$ be the integral finite adeles of $E$, and let $\mathbb{A}_f$ be the finite adeles. The finite adelic unitary group $G_f$ of the source is the group of matrices $g$ over $\mathbb{A}_f$ with $g^{\dagger} g = 1$. Its subgroup $K^{\circ}$ is the group of the $g \in G_f$ with integral entries. A space $V$ comes with a Gram matrix $J$ over $E$ and a frame $x_f$ over $\mathbb{A}_f$ with $x_f^{\dagger} J x_f = 1$. So the form of $V$ is standard in the frame $x_f$. A point $g \in G_f$ acts on rational coordinates by the matrix $x_f\, g\, x_f^{-1}$.

**Definition (Lattice of a point).** For $x \in G_f$, the lattice of $x$ is

$$\Lambda(x) = \{\, y \in \mathbb{A}_f^{\iota} : (x_f x)^{-1} y \in \hat{\mathcal{O}}^{\iota} \,\} = x_f x\, \hat{\mathcal{O}}^{\iota}.$$

Lean: `New.Space.lattice` (Lib/Weil/Periods/PointLattice.lean).

The form on finite adelic vectors is $\langle y, z \rangle = y^{\dagger} J z$. It is conjugate linear in the first variable. The frame $x_f x$ is orthonormal for this form, because $x^{\dagger} x = 1$.

**Lemma.** Each lattice $\Lambda(x)$ is self-dual: $z \in \Lambda(x)$ if and only if $\langle y, z \rangle \in \hat{\mathcal{O}}$ for all $y \in \Lambda(x)$.

Lean: `New.Space.mem_lattice_iff_formFin` (Lib/Weil/Periods/PointLattice.lean).

*Proof.* In the coordinates $c = (x_f x)^{-1} y$ and $c' = (x_f x)^{-1} z$ the form is $\langle y, z \rangle = c^{\dagger} c'$. If both coordinate vectors are integral, the sum $\sum_i \bar{c}_i c'_i$ is integral. Conversely, take $y$ to be the column $i$ of the frame. Then $\langle y, z \rangle = c'_i$, so every coordinate of $z$ is integral. $\square$

**Lemma.** For $x, x' \in G_f$, $\Lambda(x') \subseteq \Lambda(x)$ if and only if $x^{-1} x' \in K^{\circ}$. So $\Lambda(x) = \Lambda(x')$ if and only if $x^{-1} x' \in K^{\circ}$.

Lean: `New.Space.lattice_le_iff`, `New.Space.lattice_eq_iff` (Lib/Weil/Periods/PointLattice.lean).

*Proof.* The frames satisfy $(x_f x)^{-1} = (x^{-1} x')(x_f x')^{-1}$. If $\Lambda(x') \subseteq \Lambda(x)$, then each column of the frame $x_f x'$ lies in $\Lambda(x)$. Its coordinates in the frame of $x$ are the column of $x^{-1} x'$, so this matrix is integral. Conversely, an integral matrix carries integral coordinates to integral coordinates. For the equality, $K^{\circ}$ is a group, so $x^{-1} x' \in K^{\circ}$ gives $x'^{-1} x \in K^{\circ}$ and the reverse inclusion. $\square$

In the textbook, a unimodular hermitian lattice over a local ring of integers is a lattice that is its own dual. The unitary group acts transitively on such lattices in the unramified case, and the stabiliser of the standard lattice is a maximal compact subgroup. It gives O'Meara, *Introduction to Quadratic Forms*, and Jacobowitz, *Hermitian forms over local fields* (1962), as sources for the duality and for Witt's theorem on unimodular hermitian lattices. It does not give a place in these works.

**Remark (Formalization).** The lattice is a submodule over $\hat{\mathcal{O}}$ of the vectors over $\mathbb{A}_f$, and it is defined for every $x$, with no junk value. It is stated in rational coordinates, through the fixed frame $x_f$. So the lattice of the point $1$ is $x_f \hat{\mathcal{O}}^{\iota}$, and this lattice depends on the choice of $x_f$ in the structure of the space.

### The two lattices in the string part

Let $Y$ be a grading of $V$ with part $X$ and a string of length $s$, as in [Section 2](/chapter/bessel-periods/). The string spans $X^{\perp}$. Let $\pi$ be the orthogonal projection to $X^{\perp}$. It keeps the coordinates on the string and puts $0$ on the coordinates of $X$. Let $\pi_d$ be the projection to the span of the basis vectors of grade $d$.

**Definition (Graded lattice).** A lattice $L$ is graded if $\pi_d y \in L$ for every $d \in \mathbb{Z}$ and every $y \in L$.

Lean: `New.Grading.IsGraded` (Lib/Weil/Periods/PointLattice.lean).

**Definition (Intersection and projection).** For $x \in G_f$ put

$$\Lambda^{-}(x) = \Lambda(x) \cap X^{\perp}, \qquad \Lambda^{+}(x) = \pi\big(\Lambda(x)\big).$$

Write $\Lambda^{-} = \Lambda^{-}(1)$.

Lean: `New.Grading.latticeMinus`, `New.Grading.latticePlus` (Lib/Weil/Periods/PointLattice.lean).

Clearly $\Lambda^{-}(x) \subseteq \Lambda^{+}(x)$. The two lattices are dual to each other in $X^{\perp}$.

**Proposition.** Let $z \in X^{\perp}$. Then:

1. $z \in \Lambda^{-}(x)$ if and only if $\langle y, z \rangle \in \hat{\mathcal{O}}$ for all $y \in \Lambda^{+}(x)$;
2. $z \in \Lambda^{+}(x)$ if and only if $\langle y, z \rangle \in \hat{\mathcal{O}}$ for all $y \in \Lambda^{-}(x)$.

Lean: `New.Grading.mem_latticeMinus_iff_formFin`, `New.Grading.mem_latticePlus_iff_formFin` (Lib/Weil/Periods/PointLattice.lean).

*Proof.* The Gram matrix has no entries between $X$ and the string. So $\langle \pi y, z \rangle = \langle y, \pi z \rangle$. For the first part, $z \in \Lambda^{-}(x)$ means $z \in \Lambda(x)$. By self-duality this means $\langle y, z \rangle = \langle y, \pi z \rangle = \langle \pi y, z \rangle \in \hat{\mathcal{O}}$ for all $y \in \Lambda(x)$. This is the condition of part 1.

For the second part, one direction follows from part 1 and the symmetry $\overline{\langle y, z \rangle} = \langle z, y \rangle$. For the other direction, choose a basis $B$ of $X^{\perp}$ that is primitive in $\Lambda(x)$. That is, the matrix $(x_f x)^{-1} B$ is integral and has an integral left inverse $L$. Such a $B$ exists, because the ring $\hat{\mathcal{O}}$ is a product of local principal ideal rings. The columns of $B$ lie in $\Lambda^{-}(x)$, so the vector $t = B^{\dagger} J z$ of products is integral. The vector $w = (x_f x) L^{\dagger} t$ lies in $\Lambda(x)$. A direct computation gives $B^{\dagger} J (x_f x) L^{\dagger} = 1$. So $w$ and $z$ have the same products with every vector of $X^{\perp}$. The form is nondegenerate on $X^{\perp}$, so $\pi w = \pi z = z$. So $z \in \Lambda^{+}(x)$. $\square$

### Witt's theorem for the intersection

**Theorem.** Assume that $E$ contains a primitive root of unity of order $5040$. Let $x, x' \in G_f$ with $\Lambda^{-}(x) = \Lambda^{-}(x')$. Then there is a point $a$ of the finite adelic unitary group of $X$ with

$$\Lambda\big(\iota_X(a)\, x\big) = \Lambda(x'),$$

where $\iota_X$ is the embedding of the unitary group of $X$ in that of $V$.

Lean: `New.Grading.exists_lattice_inclXFin_mul_eq` (Lib/Weil/Periods/PointLattice.lean).

*Proof.* Let $B$ be a basis of $X^{\perp}$ that is primitive for $x$. Its columns span $\Lambda^{-}(x)$ over $\hat{\mathcal{O}}$. This lattice is also $\Lambda^{-}(x')$, so $B$ is primitive for $x'$ too. The coordinate matrices $T_x = (x_f x)^{-1} B$ and $T_{x'} = (x_f x')^{-1} B$ have the same Gram matrix $B^{\dagger} J B$, because both frames are orthonormal. Witt's theorem over $\hat{\mathcal{O}}$ for the standard form gives $k \in K^{\circ}$ with $k T_x = T_{x'}$ (Lean: `New.witt_Ô`). Then the point $g = x' k x^{-1}$ acts on rational coordinates by a matrix that fixes $B$. So it fixes $X^{\perp}$ pointwise.

An isometry that fixes $X^{\perp}$ pointwise also preserves $X$. So it is block diagonal, with an isometry of $X$ in the first block and $1$ in the second. So $g = \iota_X(a)$ for some $a$. Then $\iota_X(a)\, x = x' k$, so $x'^{-1}\, \iota_X(a)\, x = k \in K^{\circ}$. The last lemma gives the equality of lattices. $\square$

**Remark (Formalization).** The hypothesis `[HasPrimitiveRoot5040 E]` is an assumption on the field. By the comments of the source, it makes $E$ unramified over its real subfield at every finite place, and it gives a unit of the form $y - \bar{y}$ in the ring of integers. Witt's theorem over $\hat{\mathcal{O}}$ uses it. The register of findings records it as F-058, with no source for the constant $5040$. The textbook form of the theorem is the transitivity of the integral unitary group on unimodular sublattices with the same Gram matrix, which is a form of Witt's theorem for hermitian lattices.

### Finitely many classes under bounds

The bounds of the source compare $\Lambda^{-}(x)$ with $\Lambda^{-}$ by a finite adele $q$ and an exponent $k$.

**Definition (Lattice bounds).** For $q \in \mathbb{A}_f$ and $k \in \mathbb{N}$, the point $x$ has the lattice bounds if

$$\bar{q}^{\,k}\, \Lambda^{-} \subseteq \Lambda^{-}(x) \qquad\text{and}\qquad q^{k}\, \Lambda^{-}(x) \subseteq \Lambda^{-}.$$

The orbit of $x$ is bounded if some $r$ in the finite Bessel group $R_f$ has the property that $\Lambda(r x)$ is graded and $r x$ has the lattice bounds.

Lean: `New.Grading.HasLatticeBounds`, `New.Grading.HasBoundedOrbit` (Lib/Weil/Periods/PointLattice.lean).

Here $R_f$ is the group of finite points $r$ for which $(1, r)$ lies in the Bessel group $R$ of [Section 3](/chapter/bessel-periods/).

**Remark (Formalization).** The adele $q$ in the definition is arbitrary, and it is allowed to be $0$. For $q = 0$ and $k \geq 1$ both inclusions hold for every $x$. So the bounds say nothing in that case. The finiteness results below ask for $q$ to be a unit of $\mathbb{A}_f$. For $k = 0$ the bounds say $\Lambda^{-}(x) = \Lambda^{-}$.

**Lemma.** Let $q$ be a unit of $\mathbb{A}_f$ and let $k \in \mathbb{N}$. The set of lattices $\Lambda^{-}(x)$, for the points $x$ with the lattice bounds, is finite.

Lean: `New.Grading.finite_image_latticeMinus` (Lib/Weil/Periods/LatticeBounds.lean).

*Proof.* Put $U = \bar{q}^{\,k} \Lambda(1)$ and $C = q^{-k} \Lambda(1)$. The lattice $\Lambda(1)$ is open and compact, and $q$ is a unit. So $U$ is an open subgroup and $C$ is compact. The image of $C$ in the discrete group $\mathbb{A}_f^{\iota} / U$ is finite. By the upper bound, each $\Lambda^{-}(x)$ lies in $C$. So its image modulo $U$ is one of finitely many subsets.

It remains to show that $\Lambda^{-}(x)$ is determined by its image modulo $U$. By the lower bound, $U \cap X^{\perp} \subseteq \bar{q}^{\,k} \Lambda^{-} \subseteq \Lambda^{-}(x)$. The modular law gives

$$\big(\Lambda^{-}(x) + U\big) \cap X^{\perp} = \Lambda^{-}(x) + \big(U \cap X^{\perp}\big) = \Lambda^{-}(x).$$

So the image determines the lattice. $\square$

The source cites O'Meara, *Introduction to Quadratic Forms*, §81, for the finiteness of the lattices between two given ones and for the local nature of lattices. It does not compare the statement with that section.

The next lemma moves a point to one with a support on a finite set of places. For a set $Q$ of finite places, let $x^{Q}$ be the point with the components of $x$ at the places of $Q \cup \bar{Q}$ and with the component $1$ at the other places.

**Lemma.** Let $x$ have the lattice bounds for $q$ and $k$, and let $v(q_w) = 1$ for every place $w \notin Q$. Then $\Lambda^{-}(x^{Q}) = \Lambda^{-}(x)$.

Lean: `New.Grading.HasLatticeBounds.latticeMinus_componentOn` (Lib/Weil/Periods/LatticeBounds.lean).

*Proof.* Let $T = Q \cup \bar{Q}$. A vector $y \in X^{\perp}$ lies in a lattice if and only if its part at $T$ and its part off $T$ lie in it. At the places of $T$ the points $x^{Q}$ and $x$ have the same components, so the two lattices agree there. Off $T$ the point $x^{Q}$ has the component $1$, so its lattice agrees with $\Lambda(1)$ there. Off $T$ both $q$ and $\bar{q}$ are local units, so the two bounds say that $\Lambda^{-}(x)$ and $\Lambda^{-}$ agree there. $\square$

**Theorem.** Assume that $X$ is finite and that $E$ contains a primitive root of unity of order $5040$. Let $q$ be a unit of $\mathbb{A}_f$ with $v(q_w) = 1$ for all $w \notin Q$, and let $k \in \mathbb{N}$. Then there is a finite set $T$ of points of $G_f$, supported on $Q \cup \bar{Q}$, such that for every $x$ with bounded orbit there is $r \in R_f$ with

$$r x \in T\, K^{\circ}.$$

Lean: `New.Grading.exists_finite_representatives` (Lib/Weil/Periods/LatticeBounds.lean).

*Proof.* Let $\mathcal{B}$ be the set of points with the lattice bounds. By the lemma on finiteness, the set $\Lambda^{-}(\mathcal{B})$ is finite. So there is a finite subset $T_0 \subseteq \mathcal{B}$ with $\Lambda^{-}(T_0) = \Lambda^{-}(\mathcal{B})$. Put $T = \{ t^{Q} : t \in T_0 \}$. This set is finite and supported on $Q \cup \bar{Q}$.

Let $x$ have bounded orbit, with $r \in R_f$ such that $r x \in \mathcal{B}$. Choose $t \in T_0$ with $\Lambda^{-}(t) = \Lambda^{-}(r x)$. By the last lemma, $\Lambda^{-}(t^{Q}) = \Lambda^{-}(t)$. Witt's theorem for the intersection gives $a$ with $\Lambda(\iota_X(a)\, r x) = \Lambda(t^{Q})$. So $\iota_X(a)\, r x \in t^{Q} K^{\circ}$. The point $\iota_X(a)$ lies in $R_f$, so $\iota_X(a)\, r \in R_f$. $\square$

**Remark (Formalization).** The set $T$ is obtained by a choice of a finite subset with the same image, so it is not canonical. The proof uses only the lattice bounds of the point of the orbit. It does not use the condition that the lattice is graded, which is part of the definition of a bounded orbit. Volume 9 builds the stage cuts of the seesaw from this theorem.

### The Iwasawa decomposition

Let $\operatorname{gr}(i)$ be the grade of the basis index $i$. Say that a matrix $A$ does not lower grades if $A_{ik} = 0$ whenever $\operatorname{gr}(i) < \operatorname{gr}(k)$. Say that it raises grades if $A_{ik} = 0$ whenever $\operatorname{gr}(i) \leq \operatorname{gr}(k)$. The part of degree $0$ of $A$, written $A_0$, keeps the entries with $\operatorname{gr}(i) = \operatorname{gr}(k)$ and replaces the others by $0$. These are the conditions `HasDegreeGe` with $d = 0$ and $d = 1$ of [Section 2](/chapter/bessel-periods/).

**Lemma (Hermite form).** For every invertible matrix $Z$ over $\mathbb{A}_f$, the lattice $Z \hat{\mathcal{O}}^{\iota}$ has a basis $b$ such that $Z^{-1} b$ lies in $GL_{\iota}(\hat{\mathcal{O}})$ and neither $b$ nor $b^{-1}$ lowers grades.

Lean: `New.Grading.exists_basis_hasDegreeGe` (Lib/Weil/Periods/GradedLattice.lean).

*Proof.* Order the indices by decreasing grade. A matrix that does not lower grades is then block triangular. Over the product of local principal ideal rings $\hat{\mathcal{O}}$, there is a block triangular invertible $b$ such that $Z^{-1} b$ is primitive, that is, integral with an integral left inverse. A square primitive matrix lies in $GL_{\iota}(\hat{\mathcal{O}})$. The inverse of a block triangular matrix is block triangular. $\square$

**Lemma.** Assume that $X$ is finite and that $E$ contains a primitive root of unity of order $5040$. Let $b$ be a basis of $\Lambda(x)$ such that neither $b$ nor $b^{-1}$ lowers grades. Then there is $n \in GL_{\iota}(\hat{\mathcal{O}})$ such that $n - 1$ raises grades and

$$(b n)^{\dagger} J (b n) = b_0^{\dagger} J b_0 .$$

Lean: `New.Grading.exists_gram_mul_eq_gram_degreeZeroPart` (Lib/Weil/Periods/GradedLattice.lean).

*Proof.* The form $J$ pairs grade $d$ only with grade $-d$, and so does $J^{-1}$. Let $k = (x_f x)^{-1} b$. Then $k \in GL_{\iota}(\hat{\mathcal{O}})$, and its Gram matrix $G = k^{\dagger} k$ is $b^{\dagger} J b$. The grade conditions on $b$, $b^{-1}$ and $J$ give vanishing conditions on $G$ and on $G^{-1}$ in the entries with $\operatorname{gr}(i) + \operatorname{gr}(j) \neq 0$ on one side. A lemma of Witt type over $\hat{\mathcal{O}}$ then gives $n$ with $n - 1$ raising grades and $n^{\dagger} G n = G_0$, the part of $G$ on the entries with $\operatorname{gr}(i) + \operatorname{gr}(j) = 0$ (Lean: `New.exists_gram_eq_degreeZeroPart`). Its proof takes an orthonormal basis of the unimodular form $G_0$ and applies Witt's theorem to the basis vectors of grade at least $0$, on which $G$ and $G_0$ agree. The part of degree $0$ is multiplicative for matrices that do not lower grades, so $G_0 = b_0^{\dagger} J b_0$. $\square$

**Theorem (Iwasawa decomposition).** Assume that $X$ is finite and that $E$ contains a primitive root of unity of order $5040$. For every $x \in G_f$ there is $u \in G_f$ such that $(1, u)$ lies in the unipotent group $U$ of $Y$ and the lattice $\Lambda(u x)$ is graded.

Lean: `New.Grading.exists_isGraded` (Lib/Weil/Periods/GradedLattice.lean).

*Proof.* Take $b$ from the Hermite form for $Z = x_f x$, and $n$ from the last lemma. Let $d = b_0$ and $d' = (b^{-1})_0$. The part of degree $0$ is multiplicative here, so $d d' = 1$. Put $v = b\, n\, d'$. Then $v^{\dagger} J v = J$, by the last lemma. Also

$$v - 1 = (b - d)\, d' + b\, (n - 1)\, d',$$

and both terms raise grades. So $v$ is a unipotent isometry. Let $g \in G_f$ be the point that acts on rational coordinates by $v$. Then $(1, g) \in U$, because the matrix of $(1, g)$ minus $1$ raises grades. Put $u = g^{-1}$. Then $(1, u) \in U$, because $U$ is a group. Then $\Lambda(u x)$ is the set of $y$ with $d' y$ integral. That is, $\Lambda(u x) = d\, \hat{\mathcal{O}}^{\iota}$. The matrix $d$ has degree $0$, so it commutes with each projection $\pi_e$ to a grade. So $\Lambda(u x)$ is graded. $\square$

The textbook form is the Iwasawa decomposition $G(F_w) = P(F_w)\, K_w$ of an unramified unitary group over a local field, for the parabolic subgroup $P$ that stabilises the flag of the grades, with $K_w$ the stabiliser of a self-dual lattice. The source cites J. Tits, *Reductive groups over local fields*, Proc. Sympos. Pure Math. 33 (1979), 3.3.2, for this. The theorem above is the adelic form for the unipotent radical, with the Levi part absorbed: a lattice of the form $d\, \hat{\mathcal{O}}^{\iota}$ with $d$ of degree $0$ is exactly a graded lattice.

**Remark (Formalization).** The unipotent element acts only at the finite places: the point $(1, u)$ has the component $1$ at the infinite places. The hypothesis `[Fintype X]` is the finiteness of the index set of $X$, which the graded Gram matrix needs. The hypothesis on roots of unity enters only through the lemma of Witt type. The element $u$ is given by an existence statement, with no canonical choice. Volume 9 uses this theorem in `New.Grading.HasBoundedOrbit.of_forall` to produce a bounded orbit from bounds at graded points.
