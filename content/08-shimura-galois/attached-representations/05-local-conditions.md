---
title: Local conditions, kills and characteristic
lean:
  - Lib/GaloisRep/Main/LocalConditions.lean
  - Lib/GaloisRep/Main/AttachedRepresentations.lean
  - Lib/ClassField/Places/DecompositionCompletion.lean
  - Lib/GaloisRep/KillingPolynomials.lean
decls:
  - New.GalRep
  - New.GaloisRep.PadicPlaceEmbedding
  - New.GaloisRep.PadicPlaceEmbedding.isFrob_iff
  - New.GaloisRep.PadicPlaceEmbedding.isWeilPair_zero_iff
  - New.GaloisRep.PadicPlaceEmbedding.cyclotomicGp_eq_cyclotomicChar
  - New.exists_comap_intQpBar_eq
  - New.exists_inducesPlace
  - New.GaloisRep.decompRep
  - New.GaloisRep.IsGoodAt
  - New.GaloisRep.IsFiniteTypeAt
  - New.GaloisRep.PolyKillsAt
  - New.GaloisRep.JumpsRelAt
  - New.GaloisRep.HasJumpsAt
  - New.GaloisRep.OccursIn
  - New.GaloisRep.IsSphericalAbove
  - New.GaloisRep.IsCompatibleAt
  - New.GaloisRep.SphericalCompat
  - New.GaloisRep.IsCompatibleAt.isGoodAt
  - New.GaloisRep.IsCompatibleAt.hasJumpsAt
  - New.GaloisRep.IsCompatibleAt.polyKillsAt
  - New.GaloisRep.SphericalCompat.exists_attached
  - New.GaloisRep.SphericalCompat.isCompatibleAt
  - New.GaloisRep.isRoot_of_isRoot_charpoly
  - New.card_eq_and_charpoly_eq
  - New.GaloisRep.local_clauses_of_retract
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Local conditions, kills and characteristic

The predicate `Attached` of Section 4 is global: it speaks of most Frobenius data at once. The source states the conditions at a single place separately. This section gives them, states the proposition `SphericalCompat` of the existence theorem of Section 1, and compares the relation "the Hecke polynomial kills Frobenius" with the textbook relation "the Hecke polynomial is the characteristic polynomial of Frobenius".

### Representations and local data

**Definition (Galois representation).** For a field $E$ in $\Omega$ and a finite set $m$, an *$\ell$-adic Galois representation* of $E$ of rank $|m|$ is a group homomorphism $\Gamma_E \to \mathrm{GL}_m(\bar{\mathbb{Q}}_\ell)$.

Lean: `New.GalRep` (Lib/GaloisRep/Main/LocalConditions.lean).

**Remark (Formalization).** Continuity is not part of the definition. This is half of finding F-054. Every local condition below applies to any homomorphism, continuous or not. For the representations that the argument uses, continuity comes from condition 1 of `Attached`.

At a place $A$ of $\Omega$ above $\ell$ the source needs a map from the decomposition group to $G_\ell = \mathrm{Gal}(\bar{\mathbb{Q}}_\ell/\mathbb{Q}_\ell)$, to apply the period rings of Volume 7. It asks for this map as data.

**Definition (Local datum).** Let $A$ be a place of $\Omega$ and $D_A \subseteq \Gamma_E$ its decomposition group ([Definition](/decl/New.decompGroup/)). A *local datum at $A$* consists of:

1. a ring map $e : \Omega \to \bar{\mathbb{Q}}_\ell$ such that the integers of $\bar{\mathbb{Q}}_\ell$ pull back along $e$ to $A$;
2. a homomorphism $j : D_A \to G_\ell$ that is an open embedding and satisfies $j(g)(e(x)) = e(g x)$ for $g \in D_A$ and $x \in \Omega$.

Lean: `New.GaloisRep.PadicPlaceEmbedding` (Lib/GaloisRep/Main/LocalConditions.lean).

**Lemma.** Let $(e, j)$ be a local datum at $A$, and let $s \in D_A$.

1. For every $q$, $j(s)$ is an arithmetic Frobenius for $q$ on the integers of $\bar{\mathbb{Q}}_\ell$ if and only if $s$ is an arithmetic Frobenius at $A$ for $q$.
2. The pair $(j(s), 0)$ is a Weil pair if and only if $s$ is in the inertia group of $A$.
3. The cyclotomic character of $G_\ell$ at $j(s)$ is the $\ell$-adic cyclotomic character of $\Gamma_E$ at $s$.

Lean: `New.GaloisRep.PadicPlaceEmbedding.isFrob_iff`, `New.GaloisRep.PadicPlaceEmbedding.isWeilPair_zero_iff`, `New.GaloisRep.PadicPlaceEmbedding.cyclotomicGp_eq_cyclotomicChar` (Lib/GaloisRep/Main/LocalConditions.lean).

*Proof.* For part 1, the condition "$|x| \leq 1$ implies $|j(s)x - x^q| < 1$" is closed in $x$, since the integers are open and the open unit ball is closed in an ultrametric field. The image of $e$ is dense in $\bar{\mathbb{Q}}_\ell$, so the condition holds for all $x$ if and only if it holds for $x = e(y)$. By the equivariance of $j$ and part 1 of the datum, that is the Frobenius condition at $A$. Part 2 is part 1 with $q = 1$, since the inertia group is the set of Frobenius elements for $q = 1$ ([Definition](/decl/New.inertiaGroup/)) and a Weil pair $(t, 0)$ is an element with $t^{-1}$ a Frobenius for $1$. For part 3, $j(s)$ acts on $e(\mu_{\ell^\infty})$ as $s$ acts on $\mu_{\ell^\infty}$. $\square$

**Remark (Formalization).** Every local condition below that concerns $A$ above $\ell$ quantifies over all local data at $A$. If no local datum exists, these clauses hold vacuously. Two results remove the gap. Let $A$ be a place with $|\ell|_A < 1$.

**Lemma.** There is a ring map $e : \Omega \to \bar{\mathbb{Q}}_\ell$ such that the integers of $\bar{\mathbb{Q}}_\ell$ pull back to $A$. For such an $e$ and a number field $K$ in $\Omega$ there is a homomorphism $j$ from the decomposition group of $A$ in $\mathrm{Gal}(\Omega/K)$ to $G_\ell$ such that $(e, j)$ is a local datum.

Lean: `New.exists_comap_intQpBar_eq`, `New.exists_inducesPlace` (Lib/ClassField/Places/DecompositionCompletion.lean).

*Proof.* For the first part, take any embedding $\iota$. The place it induces and $A$ both lie over $\ell$, so they are conjugate under $\mathrm{Gal}(\Omega/\mathbb{Q})$, and a twist of $\iota$ by the conjugating element induces $A$. For the second part, let $U \subseteq G_\ell$ fix $e(K)$. Restriction along $e$ is an isomorphism from $U$ to $D_A$, and $j$ is its inverse. $\square$

The research note g, Section 9, says that existence "is proved (`exists_inducesPlace`)". That lemma takes the embedding $e$ as a hypothesis. The existence of $e$ is `New.exists_comap_intQpBar_eq`, and the two together give a local datum. The source fixes one datum by an instance in `New/Congruences` (Lean `New.Selmer.localChart`), which is finding F-044 of the register.

### The conditions at one place

Let $r$ be a Galois representation of $E$, $A$ a place of $\Omega$, and $\rho_A = r|_{D_A}$ acting on column vectors (Lean `New.GaloisRep.decompRep`, an abbreviation). Through a local datum $(e, j)$, $\rho_A$ is a representation of an open subgroup of $G_\ell$, and the notions of Volume 7 apply to it: crystalline ([Definition](/decl/New.Period.IsCrystalline/)), potentially crystalline ([Definition](/decl/New.Period.IsPotentiallyCrystalline/)), Weil pairs ([Definition](/decl/New.Period.IsWeilPair/)), the relation "kills" for the linear Frobenius ([Definition](/decl/New.Period.IsKilledBy/)) and Hodge-Tate jumps ([Definition](/decl/New.Period.jump/)), all in [period rings](/chapter/period-rings/).

**Definition (Good, finite type).** The representation $r$ is *good at $A$* if, when $\ell$ is a unit at $A$, $r$ is trivial on the inertia group of $A$, and if $\rho_A$ is crystalline along every local datum at $A$. It is *of finite type at $A$* if, when $\ell$ is a unit at $A$, $r$ is trivial on the inertia elements in some neighbourhood of $1$, and if $\rho_A$ is potentially crystalline along every local datum at $A$.

Lean: `New.GaloisRep.decompRep`, `New.GaloisRep.IsGoodAt`, `New.GaloisRep.IsFiniteTypeAt` (Lib/GaloisRep/Main/LocalConditions.lean).

**Definition (Kills).** A polynomial $P$ over $\bar{\mathbb{Q}}_\ell$ *kills $s \in \Gamma_E$ at $A$ for $r$* if

1. when $\ell$ is a unit at $A$: $P(r(s)) = 0$ as a matrix;
2. for every local datum $(e, j)$ at $A$, if $s \in D_A$, then for every $k$ such that $(j(s), k)$ is a Weil pair, $P$ kills $(s, k)$ on $\rho_A$, that is $P(\beta_{s,k}) = 0$ for the linear Frobenius $\beta_{s,k}$.

Lean: `New.GaloisRep.PolyKillsAt` (Lib/GaloisRep/Main/LocalConditions.lean).

**Definition (Jumps).** Let $R$ be a relation on $\mathbb{N}$ and let $J$ assign a multiset of integers to each embedding $E \to \mathbb{C}$. The jumps of $r$ at $A$ are *related to $J$ by $R$* if for every local datum $(e, j)$, every $g \in G_\ell$ and every $u \in \mathbb{Z}$, $R$ holds between the multiplicity of $u$ in $J(\iota_\ell^{-1} \circ g^{-1} \circ e|_E)$ and the multiplicity of $u$ as a Hodge-Tate jump of $\rho_A$ at $g$. For $R$ equality, $r$ *has the jumps $J$ at $A$*. For $R$ the relation "$a \neq 0$ implies $b \neq 0$", every member of $J$ is a jump.

Lean: `New.GaloisRep.JumpsRelAt`, `New.GaloisRep.HasJumpsAt`, `New.GaloisRep.OccursIn` (Lib/GaloisRep/Main/LocalConditions.lean).

The Lean statement of jumps uses a field map $\gamma : \bar{\mathbb{Q}}_\ell \to \mathbb{C}_\ell$ that agrees with $g$; this is how the jump at $g$ is read in Volume 7.

**Definition (Spherical above $w$).** Let $w$ be a finite place of $E$, $P$ a polynomial over $\bar{\mathbb{Q}}_\ell$, $R$ and $J$ as above. The representation $r$ is *spherical above $w$* if at every place $A$ over $w$: $r$ is good at $A$; its jumps are related to $J$ by $R$; and $P$ kills every geometric Frobenius $s$ at $A$ for $q_w$.

Lean: `New.GaloisRep.IsSphericalAbove` (Lib/GaloisRep/Main/LocalConditions.lean).

**Remark (Formalization).** The clauses for $A$ above $\ell$ do not ask that $\ell$ is not a unit; they quantify over local data, and a local datum at $A$ forces $|\ell|_A < 1$. The clauses for $\ell$ a unit at $A$ are implications. So at each place exactly one kind of clause has content, if a local datum exists above $\ell$. The docstring of `PolyKillsAt` says: "for `A` above `ℓ` the monodromy operator does not enter". The finite-type condition has no monodromy clause either; its docstring says that it corresponds to a Weil-Deligne representation with zero monodromy. This is the other half of F-054: no Weil-Deligne representation is built, and the local-global statements are in the form "kills".

### The statement of local-global compatibility

**Definition (Compatibility at a place).** Let $E$ be a CM field with a CM type, $f$ a function on $G_f$ of weight $\kappa$, $N \in \mathbb{N}$, $w$ a finite place, $r$ a Galois representation of rank $|n|$ and $A$ a place of $\Omega$. Then $r$ is *compatible with $f$ at $A$* if $r$ is good at $A$, has the jumps $J_{\kappa,N}$ of Section 2 at $A$, and, if $w$ is split and $f$ has Hecke polynomial $Q$ at $w$, then $\iota_\ell(Q)$ kills every geometric Frobenius at $A$ for $q_w$.

Lean: `New.GaloisRep.IsCompatibleAt` (Lib/GaloisRep/Main/AttachedRepresentations.lean).

**Definition (Spherical compatibility).** For a CM field $E$, a finite set $n$, $N \in \mathbb{N}$ and a finite place $w$, *spherical compatibility* is the statement: for every weight $\kappa$ and every eigenform $f$ of weight $\kappa$ on the standard definite unitary group with Hecke polynomials $P$,

1. some $r : \Gamma_E \to \mathrm{GL}_n(\bar{\mathbb{Q}}_\ell)$ is attached to $P$; and
2. if $f$ is spherical at $w$, then every $r$ attached to $P$ is compatible with $f$ at every place $A$ over $w$.

Lean: `New.GaloisRep.SphericalCompat` (Lib/GaloisRep/Main/AttachedRepresentations.lean).

**Lemma.** The definitions unfold: compatibility at $A$ gives that $r$ is good at $A$, that $r$ has the jumps $J_{\kappa,N}$ at $A$, and, for a Hecke polynomial $Q$ at a split $w$ and a geometric Frobenius $s$ at $A$, that $\iota_\ell(Q)$ kills $s$. Spherical compatibility gives an attached representation for each eigenform, and compatibility at each $A$ over $w$ for each attached $r$ when $f$ is spherical at $w$.

Lean: `New.GaloisRep.IsCompatibleAt.isGoodAt`, `New.GaloisRep.IsCompatibleAt.hasJumpsAt`, `New.GaloisRep.IsCompatibleAt.polyKillsAt`, `New.GaloisRep.SphericalCompat.exists_attached`, `New.GaloisRep.SphericalCompat.isCompatibleAt` (Lib/GaloisRep/Main/AttachedRepresentations.lean).

**Remark (Formalization).** Part 2 is stated for *every* attached $r$, not for one. With the uniqueness of traces this is natural, but the local conditions are not read off from traces. The source must prove them for each attached $r$. The rank $N$ is a separate argument; the existence theorem uses $N = |n|$. The definition applies at every place $w$, including places above $\ell$, where the Hecke clause is read through the linear Frobenius.

### Kills against characteristic

The textbook says that $\det(X - r(s)) = \iota_\ell(Q_w)$. The source says that $\iota_\ell(Q_w)(r(s)) = 0$. By Cayley-Hamilton the first implies the second. The converse fails.

**Example.** Let $r$ be the trivial representation of rank $2$ and $Q = (X - 1)(X - 2)$. Then $Q(r(s)) = Q(1) = 0$ for every $s$, so $Q$ kills every element at every place prime to $\ell$. But $\det(X - r(s)) = (X - 1)^2 \neq Q$. For an attached representation this cannot happen at most places: by Section 4, $\det(X - r(s))$ is close to $\iota_\ell(Q_w)$ for most data. It can happen at a single place $w$, since the filter says nothing about one place.

What does survive is the set of roots.

**Lemma.** Let $M$ be a square matrix over a field and $P$ a polynomial with $P(M) = 0$. Then every root of $\det(X - M)$ is a root of $P$.

Lean: `New.GaloisRep.isRoot_of_isRoot_charpoly` (Lib/GaloisRep/Main/AttachedRepresentations.lean).

*Proof.* Let $m$ be the size of $M$. The characteristic polynomial of $P(M) = 0$ is $X^m$. The polynomial $\det(X - M)$ divides $\det(X - P(M))$ evaluated at $P$, that is $P^m$ (Lean `Matrix.charpoly_dvd_charpoly_aeval_comp`). So if $\det(x - M) = 0$, then $P(x)^m = 0$, and $P(x) = 0$. $\square$

So at a spherical place $w$ prime to $\ell$, every eigenvalue of $r(s)$ is a root of $\iota_\ell(Q_w)$, a Satake parameter by Section 2. The multiplicities are not controlled, and neither is semisimplicity of $r(s)$ beyond what $Q_w$ forces: if $Q_w$ has distinct roots, then $r(s)$ is diagonalizable.

Is the exact characteristic polynomial needed? This is question Q-59 of the register. The source has one result that upgrades "kills" to "characteristic" along most Frobenius data.

**Theorem.** Let $r : \Gamma_E \to \mathrm{GL}_N(K)$ be continuous, $K$ a field, $k$ a normed field over $K$ and $n \geq 1$. Suppose:

1. the span of the image of $r$ contains every diagonal matrix;
2. for most Frobenius data $v$, the polynomial $P_v$ is monic of degree $n$ and $P_v(r(s_v)) = 0$;
3. integers $e_1, \ldots, e_n$ have no small relations: two exponent vectors of the same total degree at most $(n+1)^2$ with the same weight $\sum \alpha_i e_i$ are equal; and each $e_i$ is some $\kappa_j$;
4. for an invertible $Q$ over $k$, every polynomial in the matrix entries that vanishes at $Q\, r(g)$ for all $g$ near $1$ also vanishes at $\mathrm{diag}(T^{\kappa_j})\, Q$ over $k[T, T^{-1}]$.

Then $N$ has $n$ elements, and $\det(X - r(s_v)) = P_v$ for most Frobenius data $v$.

Lean: `New.card_eq_and_charpoly_eq` (Lib/GaloisRep/KillingPolynomials.lean).

The source uses it in `Lib/GaloisRep/Main/SeedRepresentation.lean`, lines 245 to 292, where hypothesis 4 comes from a Hodge-Tate cocharacter in the Zariski closure of the image. So for the representations built there, the characteristic polynomials are exact along most data. We do not know whether a consumer in `New` needs more than `Attached` and "kills", so Q-59 stays open in this chapter.

### Passage to subrepresentations

The local conditions pass from a representation $r'$ to a representation $r$ that embeds in it near $1$.

**Theorem.** Let $c$ be an automorphism of $\Omega$, $i : E \to E'$ a field map with $c \circ i = \mathrm{id}$ on $E$, and $\varphi : \Gamma_{E'} \to \Gamma_E$ conjugation by $c$, an open embedding. Let $P$ be a matrix with a left inverse $P'$, and let $r'(g) P = P\, r(\varphi(g))$ for $g$ in a neighbourhood $S$ of $1$. Put $A' = c^{-1}(A)$. Then:

1. if $r'$ is of finite type at $A'$, then $r$ is of finite type at $A$;
2. if also $P P' = 1$, then a relation $R$ between $J$ and the jumps passes from $r'$ at $A'$, with $J$ read on $\sigma \circ i$, to $r$ at $A$;
3. a polynomial that kills $s \in S$ for $r'$ at $A'$ kills $\varphi(s)$ for $r$ at $A$.

Lean: `New.GaloisRep.local_clauses_of_retract` (Lib/GaloisRep/Main/LocalConditions.lean).

*Proof.* For part 3 away from $\ell$: $P\, Q(r(\varphi(s))) = Q(r'(s))\, P = 0$, and multiplying by $P'$ on the left gives $Q(r(\varphi(s))) = 0$. Above $\ell$, a local datum at $A$ composed with $c$ is a local datum at $A'$, and $P$ intertwines the linear Frobenius operators, by part 3 of the properties of the linear Frobenius in [period rings](/chapter/period-rings/). Part 1 is the same argument for inertia and for potential crystallinity. Part 2 uses that $P$ is an isomorphism near $1$, so the spaces of Hodge-Tate maps of the two representations are isomorphic. $\square$

The transfer goes from $r'$ to $r$ only, and good reduction (`IsGoodAt`) is not among the clauses.
