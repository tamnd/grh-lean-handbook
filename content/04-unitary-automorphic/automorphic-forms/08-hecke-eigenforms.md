---
title: Hecke eigenforms
lean:
  - Lib/GaloisRep/Main/Defs.lean
  - Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean
  - Lib/Weil/Unramified/SplitHecke.lean
decls:
  - New.heckePoly
  - New.HasHeckePolyAt
  - New.IsEigenform
  - New.IsSphericalOff
  - New.Gf.trivialOn
  - New.exists_inf_trivialOn_le
  - New.eventually_maxCompactAt_le
  - New.hasHeckePolyAt_iff
  - New.IsUnitary.le_span_joint_eigenvectors
  - New.le_span_isSphericalOff
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Hecke eigenforms

The argument attaches to each eigenform a family of polynomials, one at each split place, from which [the attached representations](/chapter/attached-representations/) build Galois representations. This section gives the source's Hecke polynomials, its three conditions of being an eigenform, two lemmas on the places where a level is maximal, and the theorem that a finite-dimensional space of algebraic forms on a definite space, fixed by a level and stable under the Hecke operators off a finite set, is spanned by eigenforms. The notation is that of Section 7: $T_{w,j}$ is the Hecke operator at a split place $w$, $K_w$ the subgroup of $K_0$ of elements whose components away from $w$ and $\bar w$ are $1$, and $q_w$ the order of the residue field at $w$. For a finite set $S$ of places, $K_S$ is the subgroup of $G_f$ of elements whose components at the places of $S$ are $1$.

The classical model is the space of cusp forms of weight $k$ for $\Gamma_1(N)$. The Hecke operators of index prime to $N$ commute and are normal for the Petersson product, so $S_k(\Gamma_1(N))$ has an orthogonal basis of common eigenforms of the operators $T_n$ and $\langle n \rangle$ with $(n, N) = 1$ (Diamond and Shurman, *A First Course in Modular Forms* (2005), Theorem 5.5.4). The source proves the same statement for algebraic forms, with the invariant form of Section 6 in place of the Petersson product.

### Hecke polynomials

The source fixes the polynomial with the eigenvalues as coefficients.

**Definition (Hecke polynomial).** For $q, N \in \mathbb{N}$ and numbers $t_0, \dots, t_N$,
$$P_{q,N}(t) = \sum_{j=0}^{N} (-1)^j q^{j(j-1)/2}\, t_j\, X^{N-j}.$$

Lean: `New.heckePoly` (Lib/GaloisRep/Main/Defs.lean).

For $N = 2$ and $t_0 = 1$ this is $X^2 - t_1 X + q\, t_2$. For $\mathrm{GL}_2$ over $\mathbb{Q}$, with $t_1$ the eigenvalue of $T_p$ and $t_2$ that of the central operator, this has the shape of the classical Hecke polynomial $X^2 - a_p X + \chi(p) p^{k-1}$ for weight $k$ of Diamond and Shurman, Chapter 5. The source does not prove this match.

**Definition (Eigenform conditions).** Let $f$ be a function on $G_f$ with values in a vector space $M$, $w$ a split place, $P$ a polynomial, and $S$ a finite set of places.

(a) $f$ *has Hecke polynomial $P$ at $w$* if $K_w$ fixes $f$ and there are numbers $t_j$ with $T_{w,j} f = t_j f$ for all $j$ and $P = P_{q_w, n}(t)$.

(b) $f$ is an *eigenform* for a family $P = (P_w)$ if $f \neq 0$ and, for all but finitely many places $w$ whose norm $q_w$ is prime, $w$ is split and $f$ has Hecke polynomial $P_w$ at $w$.

(c) $f$ is *spherical off $S$* with polynomials $P$ if $f \neq 0$, $f$ is fixed by $K_0 \cap K_S$, where $K_S$ is the group of elements trivial at the places of $S$, and $f$ has Hecke polynomial $P_w$ at every split place $w$ with $w \notin S$ and $\bar w \notin S$.

Lean: `New.HasHeckePolyAt`, `New.IsEigenform`, `New.IsSphericalOff` (Lib/GaloisRep/Main/Defs.lean), `New.Gf.trivialOn` (Lib/Adelic/Unitary/Defs.lean).

**Remark (Formalization).** In (b) the splitting of $w$ is part of the conclusion. This loses nothing. Let $w$ be a place of $E$ of prime norm, over a place $v$ of the totally real subfield. If $w$ is inert over $v$, its norm is the square of the norm of $v$, which is not prime. So only the finitely many ramified places can have prime norm and fail to be split. In (a) the numbers $t_j$ are any numbers that make the equations hold. For $f \neq 0$ they are unique, and only $t_0, \dots, t_n$ enter $P$.

**Remark (Formalization).** The two notions of Hecke polynomial differ. The notion `New.HasHeckePolynomial` of Section 7 uses a function $p$ of $X$ and the operator $\sum_i (-X)^i q^{\binom{i}{2}} T_{w,i}$. The notion `New.HasHeckePolyAt` uses the polynomial $P_{q,n}(t)$ in the eigenvalues. For $X \neq 0$, the value of the first operator on an eigenvector is $X^n P_{q,n}(t)(1/X)$. The source uses each notion in its own part of the argument.

**Lemma.** For a form $f$ of weight $\kappa$ on a definite space and a split place $w$, $f$ has Hecke polynomial $P$ at $w$ if and only if $f$ is spherical at $w$ and there are numbers $t_j$ with $P = P_{q_w, n}(t)$ and $T_{w,j} f = t_j f$ for all $j$, with $T_{w,j}$ acting on forms.

Lean: `New.hasHeckePolyAt_iff` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean).

*Proof.* The inclusion of forms in functions commutes with the Hecke operators. $\square$

**Lemma.** Let $H$ be an open subgroup of $G_f$.

(a) There is a finite set $S$ of places with $K_0 \cap K_S \subseteq H$, such that $w \notin S$ and $\bar w \notin S$ for every $w$ with $K_w \subseteq H$.

(b) For all but finitely many places $v$, $K_v \subseteq H$.

Lean: `New.exists_inf_trivialOn_le`, `New.eventually_maxCompactAt_le` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean).

*Proof.* (a) The set $K_0 \setminus H$ is compact, and it is covered by the open sets of elements whose component at $w$ is not $1$. A finite subcover gives a finite $S$ with $K_0 \cap K_S \subseteq H$. Take $S$ minimal for inclusion. If $K_w \subseteq H$, write each element $g$ of $K_0 \cap K_{S \setminus \{w, \bar w\}}$ as $g = ab$ with $a \in K_w$ and $b$ trivial at $w$ and $\bar w$. Then $a \in H$ and $b \in K_0 \cap K_S \subseteq H$, so $S \setminus \{w, \bar w\}$ also works, and minimality gives $w, \bar w \notin S$.

(b) Take $S$ from (a). For $v$ outside the finite set $S \cup \bar S$, the group $K_v$ is trivial at all places of $S$, so $K_v \subseteq K_0 \cap K_S \subseteq H$. $\square$

### Spanning by eigenforms

**Theorem (Spectral theorem for Hecke operators).** Let $\pi$ be a representation of $G_f$ that is unitary for a positive definite hermitian form. Let $S$ be a set of split places, stable under $w \mapsto \bar w$, and $U$ a finite-dimensional subspace that is spherical at every $w \in S$ and stable under every $T_{w,j}$ with $w \in S$. Then $U$ is spanned by its vectors that are eigenvectors of all $T_{w,j}$, $w \in S$, at the same time.

Lean: `New.IsUnitary.le_span_joint_eigenvectors` (Lib/Weil/Unramified/SplitHecke.lean).

The proof uses two facts from [Iwahori exponents and Satake](/chapter/iwahori-satake/): the operators commute on vectors spherical at all places involved, and $T_{\bar w, j}$ is the adjoint of $T_{w,j}$ on spherical vectors. So each $T_{w,j}$ is normal on $U$, and a family of commuting normal operators on a finite-dimensional inner product space has a common orthonormal eigenbasis (Axler, *Linear Algebra Done Right*, 3rd edition, Chapter 7).

**Theorem.** Let $V$ be a definite space, $\kappa$ a weight, $S$ a finite set of places and $M$ a finite-dimensional space of algebraic forms of weight $\kappa$. Suppose that $K_0 \cap K_S$ fixes every element of $M$, and that $M$ is stable under $T_{w,j}$ for every split $w$ with $w, \bar w \notin S$ and every $j$. Then $M$ is spanned by its elements $f$ that are spherical off $S$ for some family $P$.

Lean: `New.le_span_isSphericalOff` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean).

*Proof.* The forms carry an invariant positive definite hermitian form, by the unitarity theorem of Section 6. Let $T$ be the set of split places $w$ with $w, \bar w \notin S$. It is stable under conjugation, and every element of $M$ is spherical at each $w \in T$, since $K_w \subseteq K_0 \cap K_S$ for such $w$. The spectral theorem gives that $M$ is spanned by joint eigenvectors $f$ with $T_{w,j} f = t_{w,j} f$. A nonzero joint eigenvector has Hecke polynomial $P_{q_w,n}(t_w)$ at each $w \in T$ by the lemma, so it is spherical off $S$. The zero vector lies in every span. $\square$

**Remark (Formalization).** The eigenforms are not chosen explicitly. The theorem asserts that the span contains $M$, and the eigenvalues come from the existence statement of the spectral theorem. The invariant form also comes from an existence statement (Section 6). The argument needs only that some spanning set of eigenforms exists.

### Where the argument uses these objects

The polynomials $P_{q,n}(t)$ and the condition of having a Hecke polynomial at a place appear in [first-order deformations](/chapter/first-order-deformations/), [the denominator bound](/chapter/denominator-bound/), [the main summands](/chapter/main-summands/) and [the attached representations](/chapter/attached-representations/). The spanning theorem is used in [first-order deformations](/chapter/first-order-deformations/). The condition of being spherical off $S$ is used in the construction of Galois representations in [building representations](/chapter/building-representations/). The two lemmas on levels have no use in the argument outside this section.
