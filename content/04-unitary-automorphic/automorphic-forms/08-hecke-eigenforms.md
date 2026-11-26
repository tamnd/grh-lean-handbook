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

The argument attaches to each eigenform one polynomial at each split place, from which [the attached representations](/chapter/attached-representations/) build Galois representations. This section gives these polynomials and shows that Hecke stable spaces of algebraic forms are spanned by eigenforms. The notation is that of Section 7: $T_{w,j}$ is the Hecke operator at a split place $w$, $K_w$ the subgroup of $K_0$ of elements whose components away from $w$ and $\bar w$ are $1$, and $q_w$ the order of the residue field at $w$. For a finite set $S$ of places, $K_S$ is the subgroup of $G_f$ of elements whose components at the places of $S$ are $1$.

The classical model: $S_k(\Gamma_1(N))$ has an orthogonal basis of common eigenforms of the $T_n$ and $\langle n \rangle$ with $(n, N) = 1$ (Diamond and Shurman, *A First Course in Modular Forms* (2005), Theorem 5.5.4). The source proves this for algebraic forms, with the invariant form of Section 6 in place of the Petersson product.

### Hecke polynomials

**Definition (Hecke polynomial).** For $q, N \in \mathbb{N}$ and numbers $t_0, \dots, t_N$,
$$P_{q,N}(t) = \sum_{j=0}^{N} (-1)^j q^{j(j-1)/2}\, t_j\, X^{N-j}.$$

Lean: `New.heckePoly` (Lib/GaloisRep/Main/Defs.lean).

For $N = 2$ and $t_0 = 1$ this is $X^2 - t_1 X + q\, t_2$, the shape of the classical $X^2 - a_p X + \chi(p) p^{k-1}$ of Diamond and Shurman, Chapter 5. The source does not prove this match.

**Definition (Eigenform conditions).** Let $f$ be a function on $G_f$ with values in a vector space $M$, $w$ a split place, $P$ a polynomial, and $S$ a finite set of places.

(a) $f$ *has Hecke polynomial $P$ at $w$* if $K_w$ fixes $f$ and there are numbers $t_j$ with $T_{w,j} f = t_j f$ for all $j$ and $P = P_{q_w, n}(t)$.

(b) $f$ is an *eigenform* for a family $P = (P_w)$ if $f \neq 0$ and, for all but finitely many places $w$ whose norm $q_w$ is prime, $w$ is split and $f$ has Hecke polynomial $P_w$ at $w$.

(c) $f$ is *spherical off $S$* with polynomials $P$ if $f \neq 0$, $f$ is fixed by $K_0 \cap K_S$ and $f$ has Hecke polynomial $P_w$ at every split place $w$ with $w \notin S$ and $\bar w \notin S$.

Lean: `New.HasHeckePolyAt`, `New.IsEigenform`, `New.IsSphericalOff` (Lib/GaloisRep/Main/Defs.lean), `New.Gf.trivialOn` (Lib/Adelic/Unitary/Defs.lean).

**Remark (Formalization).** In (b) the splitting of $w$ is part of the conclusion. This loses nothing: an inert place has norm a square, which is not prime, so only finitely many ramified places are excluded. In (a), for $f \neq 0$ the $t_j$ are unique.

**Remark (Formalization).** `New.HasHeckePolynomial` of Section 7 uses the operator $\sum_i (-X)^i q^{\binom{i}{2}} T_{w,i}$, and `New.HasHeckePolyAt` uses $P_{q,n}(t)$. On an eigenvector, for $X \neq 0$, the first is $X^n P_{q,n}(t)(1/X)$.

**Lemma.** For a form $f$ of weight $\kappa$ on a definite space and a split place $w$, $f$ has Hecke polynomial $P$ at $w$ if and only if $f$ is spherical at $w$ and there are numbers $t_j$ with $P = P_{q_w, n}(t)$ and $T_{w,j} f = t_j f$ for all $j$, with $T_{w,j}$ acting on forms.

Lean: `New.hasHeckePolyAt_iff` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean).

*Proof.* The inclusion of forms in functions commutes with the Hecke operators. $\square$

**Lemma.** Let $H$ be an open subgroup of $G_f$.

(a) There is a finite set $S$ of places with $K_0 \cap K_S \subseteq H$, such that $w \notin S$ and $\bar w \notin S$ for every $w$ with $K_w \subseteq H$.

(b) For all but finitely many places $v$, $K_v \subseteq H$.

Lean: `New.exists_inf_trivialOn_le`, `New.eventually_maxCompactAt_le` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean).

*Proof.* (a) By compactness of $K_0$ there is a finite $S$ with $K_0 \cap K_S \subseteq H$. Take $S$ minimal. If $K_w \subseteq H$, then $K_0 \cap K_{S \setminus \{w, \bar w\}} = K_w \cdot (K_0 \cap K_S) \subseteq H$, so minimality gives $w, \bar w \notin S$. (b) For $v \notin S \cup \bar S$, $K_v \subseteq K_0 \cap K_S \subseteq H$. $\square$

### Spanning by eigenforms

**Theorem (Spectral theorem for Hecke operators).** Let $\pi$ be a representation of $G_f$ that is unitary for a positive definite hermitian form. Let $S$ be a set of split places, stable under $w \mapsto \bar w$, and $U$ a finite-dimensional subspace that is spherical at every $w \in S$ and stable under every $T_{w,j}$ with $w \in S$. Then $U$ is spanned by its vectors that are eigenvectors of all $T_{w,j}$, $w \in S$, at the same time.

Lean: `New.IsUnitary.le_span_joint_eigenvectors` (Lib/Weil/Unramified/SplitHecke.lean).

By [Iwahori exponents and Satake](/chapter/iwahori-satake/), the operators commute and $T_{\bar w, j}$ is the adjoint of $T_{w,j}$, so they are commuting normal operators on $U$ and have a common orthonormal eigenbasis (Axler, *Linear Algebra Done Right*, 3rd edition, Chapter 7).

**Theorem.** Let $V$ be a definite space, $\kappa$ a weight, $S$ a finite set of places and $M$ a finite-dimensional space of algebraic forms of weight $\kappa$. Suppose that $K_0 \cap K_S$ fixes every element of $M$, and that $M$ is stable under $T_{w,j}$ for every split $w$ with $w, \bar w \notin S$ and every $j$. Then $M$ is spanned by its elements $f$ that are spherical off $S$ for some family $P$.

Lean: `New.le_span_isSphericalOff` (Lib/Adelic/AutomorphicForms/HeckeEigenforms.lean).

*Proof.* The forms are unitary by Section 6. Let $T$ be the set of split $w$ with $w, \bar w \notin S$. Then $T$ is stable under conjugation and $M$ is spherical at each $w \in T$. The spectral theorem spans $M$ by joint eigenvectors, and by the lemma a nonzero one is spherical off $S$. $\square$

**Remark (Formalization).** The eigenforms are not chosen explicitly. The eigenvalues and the invariant form come from existence statements, and the argument needs only that a spanning set of eigenforms exists.

### Where the argument uses eigenforms

Hecke polynomials appear in [first-order deformations](/chapter/first-order-deformations/), which also uses the spanning theorem, [the denominator bound](/chapter/denominator-bound/), [the main summands](/chapter/main-summands/) and [the attached representations](/chapter/attached-representations/). [Building representations](/chapter/building-representations/) uses forms spherical off $S$.
