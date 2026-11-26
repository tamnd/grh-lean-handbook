---
title: Hermitian spaces and unitary groups
lean:
  - Lib/Adelic/Landherr.lean
  - Lib/Adelic/Witt/WittTheorem.lean
  - Lib/Adelic/Witt/IwasawaDecomposition.lean
  - Lib/General/Groups/CongruenceSubgroups.lean
decls:
  - New.U
  - New.USign
  - New.signMatrix
  - New.intGL
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Hermitian spaces and unitary groups

This section gives the classical theory of hermitian spaces over a CM extension, and of their unitary groups over the adeles. It states the local classification, Landherr's theorem, Witt's theorem and the Iwasawa decomposition. The source proves special cases of the last three. Sections 5 and 6 state these cases and compare them with the classical forms of this section.

### Hermitian forms and their matrices

Let $E$ be a CM field with maximal real subfield $F = E^+$, and write $x \mapsto \bar x$ for complex conjugation on $E$. A *hermitian form* on a vector space $V$ of dimension $n$ over $E$ is a map $h : V \times V \to E$ that is linear in the second variable and that satisfies $h(y, x) = \overline{h(x, y)}$. So $h$ is conjugate linear in the first variable, and $h(x, x)$ lies in $F$. The form is *nondegenerate* if $h(x, y) = 0$ for all $y$ implies $x = 0$. A *hermitian space* is a pair $(V, h)$ with $h$ nondegenerate.

In a basis of $V$, the form is $h(u, v) = u^* J v$, where $u^* = \bar u^{\,t}$ and $J$ is the Gram matrix of the basis. The matrix is hermitian, $J^* = J$, and it is invertible exactly when $h$ is nondegenerate. A change of basis by $a \in \mathrm{GL}_n(E)$ replaces $J$ by $a^* J a$. So the isometry classes of hermitian spaces of dimension $n$ are the classes of invertible hermitian matrices under $J \sim a^* J a$. The determinant of $a^* J a$ is $N(\det a) \det J$, where $N(t) = t\bar t$ is the norm from $E$ to $F$. So the class of $\det J$ in $F^\times / N(E^\times)$ is an invariant, the *discriminant*.

A vector $x \neq 0$ is *isotropic* if $h(x, x) = 0$. A *hyperbolic plane* is a space of dimension $2$ with a basis $k, l$ of isotropic vectors with $h(l, k) = 1$. Its Gram matrix is $\begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$. Each nondegenerate space has a *Witt decomposition*: $V = (L \oplus L') \perp V_0$, where $L$ and $L'$ are totally isotropic of the same dimension $p$, paired perfectly by $h$, and $V_0$ has no isotropic vector. The number $p$ is the *Witt index*.

**Definition (Unitary group of a matrix).** Let $R$ be a commutative ring with an involution $x \mapsto \bar x$, and let $J$ be a square matrix over $R$. The *unitary group* $U(J)$ is the group of invertible matrices $g$ with $g^* J g = J$. For a family $s$ of signs $s_i = \pm 1$, the *sign matrix* is $\mathrm{diag}(s)$, and $U(\mathrm{diag}(s))$ is the group $U(p, q)$ over $\mathbb{C}$, with $p$ and $q$ the numbers of signs $+1$ and $-1$. For a subring $O$ of $R$, the group $\mathrm{GL}_n(O)$ is the group of matrices that have, with their inverses, entries in $O$.

Lean: `New.U`, `New.USign`, `New.signMatrix`, `New.intGL` (Lib/General/Groups/CongruenceSubgroups.lean).

The definition does not ask that $J$ is hermitian or invertible. The source uses it for hermitian $J$ over $E$, over the adeles of $E$ and over $\mathbb{C}$.

### The local theory

Let $v$ be a place of $F$. The algebra $E_v = E \otimes_F F_v$ is of one of three kinds, and the hermitian spaces over it are classified as follows.

1. *Split.* The place $v$ splits into two places $w \neq \bar w$ of $E$. Then $E_v = F_v \times F_v$, and conjugation exchanges the factors. A hermitian matrix is a pair $(A, A^t)$, so it is determined by one invertible matrix $A$ over $F_v$. All hermitian spaces of dimension $n$ are isometric. The unitary group is $\mathrm{GL}_n(F_v)$: the isomorphism sends $g = (g_w, g_{\bar w})$ to $g_w$, and the inverse sends $a$ to $(a, (a^t)^{-1})$ for the identity form.
2. *Finite and not split.* The place $v$ is finite and $E_w / F_v$ is a quadratic field extension. Two hermitian spaces of the same dimension are isometric if and only if their discriminants are equal in $F_v^\times / N(E_w^\times)$. This group has order $2$ by local class field theory. Each class occurs in each dimension $n \geq 1$.
3. *Real.* The place $v$ is real, and $E_w = \mathbb{C}$. A hermitian space is classified by its signature $(p, q)$, by Sylvester's law of inertia. The unitary group is $U(p, q)$.

The second case is in Jacobowitz, *Hermitian forms over local fields*, Amer. J. Math. 84 (1962), which also classifies the hermitian lattices. One fact of that theory is used often below. If $E_w / F_v$ is unramified, then every unit of $\mathcal{O}_{F_v}$ is a norm of a unit of $\mathcal{O}_{E_w}$, and every unimodular hermitian lattice has an orthonormal basis. So, at an unramified place, there is one unimodular lattice of each rank up to isometry, the lattice $\mathcal{O}_{E_w}^n$ with the identity form.

### Landherr's theorem

The global classification is a Hasse principle.

**Theorem (Landherr).** Let $E / F$ be a quadratic extension of number fields, and let $V$ and $W$ be hermitian spaces over $E$ of the same dimension. Then $V$ and $W$ are isometric if and only if $V \otimes_F F_v$ and $W \otimes_F F_v$ are isometric for every place $v$ of $F$. For a CM field $E$, this holds if and only if $V$ and $W$ have the same discriminant in $F^\times / N(E^\times)$ and the same signature at each real place of $F$.

Lean: the source proves a special case, `New.Space.landherr` (Lib/Adelic/Landherr.lean).

The theorem is in W. Landherr, *Äquivalenz Hermitescher Formen über einem beliebigen algebraischen Zahlkörper*, Abh. Math. Sem. Hamburg 11 (1936), 245 to 248. The second form follows from the first by the local classification and by Hasse's norm theorem: an element of $F^\times$ is a norm from $E$ if and only if it is a norm at every place, since $E / F$ is cyclic. One classical route reduces the theorem to the Hasse-Minkowski theorem for the quadratic form $x \mapsto h(x, x)$ on $V$, a form of dimension $2n$ over $F$. Another route uses the Galois cohomology of the unitary group. The source cites M. Kneser, *Lectures on Galois cohomology of classical groups*, Tata Institute 47 (1969), §5.5, for the second route. The source does not use either route. Section 6 gives its proof, by the norm theorem and strong approximation.

### Witt's theorem

**Theorem (Witt).** Let $V$ be a nondegenerate hermitian space over a field with a nontrivial involution. Every isometry between two subspaces of $V$ extends to an isometry of $V$. In matrices: let $J$ be an invertible hermitian $n \times n$ matrix and let $X$, $Y$ be $n \times k$ matrices of rank $k$ with $X^* J X = Y^* J Y$. Then $gX = Y$ for some $g \in U(J)$.

Lean: the source proves the matrix form, `New.witt` (Lib/Adelic/Witt/WittTheorem.lean).

The theorem goes back to Witt for quadratic forms. The source cites U. A. First, *Witt's extension theorem for quadratic spaces over semiperfect rings*, J. Pure Appl. Algebra 219 (2015), Corollary 4.9, and the list of references of the source records that this place was compared. For fields the source cites Dieudonné, *La géométrie des groupes classiques* (1955).

Two consequences are used often. First, the Witt index of $V$ and the isometry class of the anisotropic part $V_0$ are invariants. Second, every totally isotropic subspace with a basis $k_1, \dots, k_p$ is part of a Witt decomposition: there are isotropic $l_1, \dots, l_p$ with $h(l_i, k_j) = \delta_{ij}$, and the orthogonal complement $V_0$ of all of them is nondegenerate.

Over a ring the statement can fail. Over $\mathcal{O}_{E_w}$ at an unramified place it holds for the unimodular lattice $\mathcal{O}_{E_w}^n$ and *primitive* frames, those that extend to a basis of the lattice. This is the integral form that Section 5 proves.

### Unitary groups over the adeles

Let $V$ be a hermitian space over $E$ with Gram matrix $J$ in a basis. The unitary group $U(V)$ is an algebraic group over $F$: for an algebra $R$ over $F$, its points are $U(V)(R) = \{g \in \mathrm{GL}_n(E \otimes_F R) : g^* J g = J\}$. Since $E \otimes_F \mathbb{A}_F = \mathbb{A}_E$, the adelic points are
$$U(V)(\mathbb{A}_F) = \{g \in \mathrm{GL}_n(\mathbb{A}_E) : g^* J g = J\},$$
where the involution of $\mathbb{A}_E$ is conjugation, which permutes the places of $E$. This group is the restricted product of the local groups $U(V)(F_v)$ with respect to the stabilizers of the completions of one lattice. At a real place $v$ it is $U(p_v, q_v)$, and at a split place it is $\mathrm{GL}_n(F_v)$.

The rational points $U(V)(F)$ form a discrete subgroup of $U(V)(\mathbb{A}_F)$. The quotient has finite volume, since $U(V)$ has no rational characters. It is compact if and only if $V$ has no isotropic vector. If $V$ is *definite*, that is, positive definite at every real place, then $U(V)(F_\infty)$ is compact, and for every compact open subgroup $K$ of $U(V)(\mathbb{A}_{F,f})$ the set of classes $U(V)(F) \backslash U(V)(\mathbb{A}_{F,f}) / K$ is finite. Platonov and Rapinchuk, *Algebraic Groups and Number Theory*, Chapter 5, prove these facts for reductive groups. The forms on definite groups of Theorems A and C live on these finite class sets. [Quotients and reduction theory](/chapter/reduction-theory/) gives the forms of these facts that the source proves.

### The Iwasawa decomposition

Let $V = (L \oplus L') \perp V_0$ be a Witt decomposition, and let $P$ be the stabilizer of $L$ in $U(V)$. It is a parabolic subgroup. Its Levi factor $M \cong \mathrm{GL}(L) \times U(V_0)$ acts on $L$ by $m$, on $L'$ by the inverse of the adjoint of $m$, and on $V_0$ by $U(V_0)$. Its unipotent radical $N$ fixes $L$ and $L^\perp / L$.

**Theorem (Iwasawa decomposition).** Let $K = \prod_v K_v$ be a maximal compact subgroup of $U(V)(\mathbb{A}_F)$, with $K_v$ a special maximal compact subgroup for almost all $v$ in good position with respect to $P$. Then $U(V)(\mathbb{A}_F) = P(\mathbb{A}_F)\, K = N(\mathbb{A}_F)\, M(\mathbb{A}_F)\, K$.

Lean: the source proves a form for its groups, `New.Space.Splitting.iwasawa` (Lib/Adelic/Witt/IwasawaDecomposition.lean).

At a real place this is the Iwasawa decomposition of a real reductive group. At a finite place it is a property of good maximal compact subgroups in the sense of Bruhat and Tits. The source cites J. Tits, *Reductive groups over local fields*, Proc. Sympos. Pure Math. 33 (1979), part 1, 3.3.2 and 3.8.1, and its list of references records that this place was compared. Section 5 explains why, for the groups of the source, the decomposition follows from Witt's theorem at each place.

### What the source changes

The classical theory works with all hermitian spaces and with the algebraic group $U(V)$ over $F$. The source works with matrices over $E$ and over the adeles of $E$, and with one standard form at each place. The next section gives these definitions. The main restriction is that every space of the source is the identity form at every finite place. By the local theory, a space over a CM field with this property has, at each nonsplit finite place, the discriminant of the identity, so its discriminant is a local norm at every finite place. If $E / F$ is unramified at every finite place, the identity is the only unimodular form at each such place, so the restriction says that the space has a unimodular lattice at every finite place.
