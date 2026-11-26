---
title: Base change and odd rank
lean:
  - Lib/GaloisRep/BaseChange/CommutingHeckeFamilies.lean
  - Lib/GaloisRep/BaseChange/PrimeDegreeTransfer.lean
  - Lib/GaloisRep/BaseChange/TwistedTraceIdentity.lean
  - Lib/GaloisRep/Hilbert90/UnitaryGroups.lean
  - Lib/GaloisRep/Main/QuadraticStep.lean
  - Lib/GaloisRep/Main/OddRank.lean
decls:
  - New.IsStep
  - New.IsWeakBaseChange
  - New.twisted_trace_identity
  - New.exists_isWeakBaseChange_of_matching
  - New.hilbert90_finite_idele
  - New.GaloisRep.exists_weak_baseChange
  - New.GaloisRep.exists_isStep_hasQuadSubfield
  - New.GaloisRep.exists_attached_of_open_subgroups
  - New.GaloisRep.sphericalCompat_of_odd
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Base change and odd rank

The split case of Section 3 needs a field that contains $\mathbb Q(\sqrt{-D})$, and it needs $\ell$ and the place $w$ to lie over split primes of that field. A general CM field $E$ does not have this property. This section moves a form from $E$ to an extension $E'$ that has it, applies the split case over $E'$, and moves the representation back. Two tools do this. The first is base change of forms along a cyclic extension of prime degree. The second is a gluing lemma for representations of open subgroups. The result is [the theorem in odd rank](/decl/New.GaloisRep.sphericalCompat_of_odd/).

### Steps

The source does base change one cyclic step at a time.

**Definition (Step).** Let $E$ be a CM field and $E'$ an extension of $E$. Let $\mu$ be a character of the finite ideles $\mathbb A_{E,f}^\times$. The pair $(E', \mu)$ is a *step* over $E$ if:

1. $E$ contains a primitive root of unity of order $5040$;
2. $E'$ is a CM field, Galois over $E$ of prime degree;
3. some integer of $E'$ has trace $1$ to $E$;
4. $\mu$ has open kernel and is trivial on $E^\times$;
5. for a finite idele $z$, $\mu(z\bar z) = 1$ exactly when $z$ is a principal idele times a norm from $E'$.

Lean: `New.IsStep` (Lib/GaloisRep/BaseChange/CommutingHeckeFamilies.lean).

Condition 5 says that $\mu$ is a character of the class field of $E'/E$, read on the elements $z\bar z$. Condition 3 asks only for one integer of trace $1$.

### Weak base change

The textbook statement of base change for unitary groups compares orbital integrals and twisted orbital integrals. See Arthur and Clozel, *Simple algebras, base change, and the advanced theory of the trace formula*, Ann. of Math. Studies 120 (1989), and Labesse, *Changement de base CM et séries discrètes* (2011), Corollary 5.3. The source proves a weaker statement for definite unitary groups, through a twisted trace identity on spaces of forms.

**Definition (Weak base change).** Let $(E', \mu)$ be a step, $f$ a form over $E$ and $f'$ a form over $E'$. Let $Z$ be a set of finite places of $E$. Then $f'$ is a *weak base change* of $f$ off $Z$ if $Z$ is finite and, for every place $w$ of $E$ outside $Z \cup \bar Z$ and every place $u$ of $E'$ above $w$:

1. if $w$ is unramified in the step and $f$ is spherical at $w$, then $f'$ is spherical at $u$;
2. if $w$ is *matched* and split, then $u$ is split and every Hecke polynomial of $f$ at $w$ is a Hecke polynomial of $f'$ at $u$.

Here $w$ is matched if $\mu$ is trivial on $E_w^\times$, and each place above $w$ has the norm of $w$ and is moved by every $\sigma \neq 1$ in $\operatorname{Gal}(E'/E)$.

Lean: `New.IsWeakBaseChange` (Lib/GaloisRep/BaseChange/PrimeDegreeTransfer.lean).

The definition says nothing at places of $E$ that do not split completely in $E'$. At a matched place, $E'_u = E_w$, so the local groups are the same and the Hecke polynomials can be compared directly. This is the case that the representations need. A Frobenius element at such a place lies in the subgroup $\operatorname{Gal}(\Omega/E')$.

**Theorem (Twisted trace identity).** Let $(E', \mu)$ be a step and let $\sigma \neq 1$ in $\operatorname{Gal}(E'/E)$. Let $L \leq K$ be subgroups of the standard level over $E'$, with $L$ open and $\sigma$-stable. Suppose every $s \in K$ of twisted norm $1$ along $\sigma$ has the form $s = t\,\sigma(t)^{-1}$ with $t \in K$. Then there are $c \neq 0$ and an operator $t$ on forms of weight $\kappa'$ over $E'$, where $\kappa'$ is the weight $\kappa$ pulled back to $E'$, such that:

1. $t$ turns right translation by $g$ into right translation by $\sigma(g)$;
2. $t$ keeps the forms fixed by $L$;
3. for every matching pair $(\varphi, f)$ of functions, with Hecke operators $T'$ of $\varphi$ and $T$ of $f$ on the fixed vectors, $\operatorname{tr}(T' t) = c \operatorname{tr} T$.

Lean: `New.twisted_trace_identity` (Lib/GaloisRep/BaseChange/TwistedTraceIdentity.lean).

The traces are traces on finite-dimensional spaces of forms, since the groups are definite. So the identity is an equality of finite sums over double cosets. There is no analysis and no stabilization. The hypothesis on $K$ is a Hilbert 90 statement for the level. The source proves Hilbert 90 for the unitary group with a congruence condition (Lean: `New.unitary_hilbert90_at_level`) and uses it to split these cocycles at congruence levels (Lean: `New.cocyclesSplit_and_isMatchingPair_of_congruence`). It also proves the version for ideles.

**Lemma (Hilbert 90 for finite ideles).** Let $L/K$ be an extension of number fields and let $\sigma \in \operatorname{Gal}(L/K)$ have order $n$. Let $u$ be a finite adele of $L$ with $\prod_{i<n} \sigma^i(u) = 1$. Then there is an invertible finite adele $c$ with $u\,\sigma(c) = c$.

Lean: `New.hilbert90_finite_idele` (Lib/GaloisRep/Hilbert90/UnitaryGroups.lean).

For fields this is Hilbert's Theorem 90 for a cyclic group (Serre, *Corps locaux*, Chapter X, §1). The source proves the idele version by Galois descent for the semilinear map $x \mapsto u\,\sigma(x)$. Two fixed points of this map have a common divisor that is again fixed, and this gives a fixed unit.

The twisted trace identity, applied to matching local data, gives the base change.

**Theorem (Base change in prime degree).** Let $(E', \mu)$ be a step with $E'$ that contains a primitive root of unity of order $5040$. Let $f$ be a form of weight $\kappa$ over $E$, and let $F$, $F'$ be matching local data above a set $Z$, with levels $L$ and $L'$. Suppose the Hecke operators of the families commute, the families are stable under products with the operators of a family $o$, and a chosen operator $F_{j_0}$ has nonzero trace on the generalized eigenspace of $f$ for eigenvalues $\theta$. Then some eigenform $g \neq 0$ over $E'$ of weight $\kappa'$ is a weak base change of $f$ off $Z$, is fixed by $L'$ with eigenvalues $\theta$ for the family $F' \circ o$, and lies in the image of the operator of $F'_{j_0}$.

Lean: `New.exists_isWeakBaseChange_of_matching` (Lib/GaloisRep/BaseChange/PrimeDegreeTransfer.lean).

*Proof.* The operator $t$ commutes with every operator of $F' \circ o$ up to $\sigma$. So it preserves the generalized eigenspace $Y'$ for $\theta$ over $E'$. The trace identity gives $\operatorname{tr}(F'_{j_0} t \mid Y') = c\,\operatorname{tr}(F_{j_0} \mid Y)$. The right side is not zero, by hypothesis. So $Y' \neq 0$, and $Y'$ contains an eigenvector $g$ for the commuting operators. The operators at matched places are matched by the local data, so their eigenvalues on $g$ agree with those on $f$. $\square$

Odd rank uses the simplest case.

**Corollary (Weak base change with no exceptions).** Let $(E', \mu)$ be a step with $E'$ that contains a primitive root of unity of order $5040$. Let $f \neq 0$ be a form of weight $\kappa$ over $E$. Then there are an eigenform $F$ over $E'$ of weight $\kappa'$ and Hecke polynomials $P'$ of $F$ such that $F$ is a weak base change of $f$ off the empty set.

Lean: `New.GaloisRep.exists_weak_baseChange` (Lib/GaloisRep/Main/OddRank.lean).

### Quadratic steps

The next proposition chooses the step. A character $\chi$ of $\operatorname{Gal}(\Omega/E)$ with values in $\mathbb Q/\mathbb Z$ defines the field $E' = E_\chi$ fixed by the kernel of $g \mapsto \chi(g) + \chi(c g c^{-1})$, with $c$ complex conjugation. Let $U$ be this kernel and $N = U \cap \ker\chi$.

**Proposition (Quadratic steps exist).** Let $E$ be a CM field that contains a primitive root of unity of order $5040$, and let $n \neq 0$ be an integer. There are $\chi$ and $D \equiv 3 \bmod 4$ such that $E' = E_\chi$ contains $\mathbb Q(\sqrt{-D})$ and:

1. $E'$ with the idele character of $\chi$ is a step over $E$;
2. for some $m$, every subgroup that contains the inertia groups at the places of norm at most $m$ prime to $n$ meets every coset of $N$;
3. every place of $E'$ above $n$ lies over a split prime of $\mathbb Q(\sqrt{-D})$ prime to $D$;
4. at every place $w$ above $n$, the decomposition group lies in $U$, the inertia group lies in $N$, and if $w$ is split, the decomposition group lies in $N$.

Lean: `New.GaloisRep.exists_isStep_hasQuadSubfield` (Lib/GaloisRep/Main/QuadraticStep.lean).

The proof uses the Grunwald-Wang theorem of the source (lean:Lib/ClassField/Grunwald.lean) and [class field theory](/chapter/class-field-theory/) to build $\chi$ with prescribed local behaviour at the places above $n$. Part 3 makes the split case apply over $E'$ at every place above $n$. Part 4 says that $E'/E$ is split completely above $n$, so that the places above $n$ are matched. Part 2 is the input for gluing.

### Gluing

**Lemma (Gluing representations of open subgroups).** Let $N_0$ be a normal subgroup of $\operatorname{Gal}(\Omega/E)$, and let $N_T$ for $T \in \mathbb N$ be open normal subgroups. Let $\rho_0$ on $N_0$ and $\rho_T$ on $N_T$ be attached to the same Hecke polynomials $P$. Let $I$ be a set such that:

1. every subgroup that contains $I$ meets every coset of $N_0$;
2. every conjugate of an element of $I$ lies in every $N_T$ and is killed by $\rho_T$;
3. every arithmetic Frobenius element at a place of prime norm lies in some $N_T$.

Then some representation of $\operatorname{Gal}(\Omega/E)$ is attached to $P$.

Lean: `New.GaloisRep.exists_attached_of_open_subgroups` (Lib/GaloisRep/Main/OddRank.lean).

*Proof.* Let $K$ be the largest normal subgroup inside the kernels of all the $\rho_T$. It contains the conjugates of $I$, so by condition 1, for every $g$ there is $\sigma(g) \in K$ with $g\sigma(g) \in N_0$. Where $\rho_0$ and $\rho_T$ are both defined, they have the same trace, since they are attached to the same $P$. A representation with a non-degenerate trace form is determined up to conjugation by its trace, so $\rho_0$ kills $K \cap N_0$. Then $R(g) = \rho_0(g\sigma(g))$ is well defined and is a homomorphism that extends $\rho_0$. It is continuous, since it agrees with $\rho_0$ on the open subgroup $N_0$. It is attached to $P$ at the Frobenius elements of condition 3, by comparison with the $\rho_T$. $\square$

### Odd rank

**Theorem (Odd rank).** Let $a$ be odd, let $E$ be a CM field that contains a primitive root of unity of order $5040$, and let $w$ be a finite place. Then $\mathrm{SphericalCompat}$ holds for $E$, rank $a$ and $w$.

Lean: `New.GaloisRep.sphericalCompat_of_odd` (Lib/GaloisRep/Main/OddRank.lean).

*Proof.* Let $f$ be an eigenform with Hecke polynomials $P$. It is fixed by the integral points that are trivial at a finite set $S$ of places. For each $T \in \mathbb N$ let $n_T$ be divisible by $\ell$, by $w$, by the places of $S$, and by all places of norm at most $T$. Choose a quadratic step $\chi_T$ for $n_T$, with field $E_T \supseteq \mathbb Q(\sqrt{-D_T})$. By the corollary, $f$ has a weak base change $F_T$ over $E_T$. Since $\ell$ divides $n_T$, part 3 of the proposition shows that the split case applies over $E_T$ at every place above $n_T$. So the split case gives a representation $r_T$ of $\operatorname{Gal}(\Omega/E_T)$ attached to the Hecke polynomials of $F_T$. Its restriction $\rho_T$ to $\ker\chi_T \cap U_T$ is attached to $P$, since Frobenius elements in this group are at matched places. Now apply the gluing lemma with $N_0$ from $T = 0$, $N_T$ from $T + m$, and $I$ the inertia groups at small places prime to $n_0$. The representation $r_{T+m}$ is unramified at these places, because they divide $n_{T+m}$ and $F_{T+m}$ is spherical there. A place of prime norm $q$ divides $n_{q+m}$, so its Frobenius element lies in $N_{q+m}$. The local clause at $w$ descends from the step $T = 0$, where the decomposition group at $w$ fixes $E_0$. $\square$

**Remark (Formalization).** The odd rank theorem has only `[HasPrimitiveRoot5040 E]` as a field hypothesis. The steps $E_T$ inherit it from $E$, since they contain $E$. The theorem is stated for every finite place $w$, but the conclusion at $w$ has content only when the form is spherical at $w$. The source uses no base change to $\mathrm{GL}_n$ and no base change of non-spherical local data in odd rank: the corollary uses the empty exceptional set.
