---
title: Cochains and the local theory
lean:
  - Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean
  - Lib/ClassField/GaloisCohomology/TateIndexFormula.lean
  - Lib/ClassField/Places/GaloisDefs.lean
  - Lib/ClassField/Local/InvariantMap.lean
  - Lib/ClassField/Local/ArtinMap.lean
decls:
  - New.H2
  - New.QZ
  - New.QZ.carry
  - New.QZ.carry_add_add_carry
  - New.QZChar
  - New.cyclicClass
  - New.QZChar.abelianLift
  - New.IsLocalGalois
  - New.ordRat
  - New.IsClassOfInvariant
  - New.Cohomology.classOfInvariant
  - New.cokerKerIndex
  - New.Tate.index_formula
  - New.tate_index_formula_norm
  - New.IsLocalGalois.mem_zmultiples_of_index_prime
  - New.IsLocalGalois.isClassOfInvariant_classOfInvariant
  - New.IsLocalGalois.classOfInvariant_bijective
  - New.Cohomology.resH2_classOfInvariant
  - New.IsLocalArtin
  - New.localArtin
  - New.IsLocalArtin.exists_frob_of_isUniformiser
  - New.IsPlaceOver.isLocalArtin_localArtin
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Cochains and the local theory

This section explains the local half of the theory: the Brauer group of a local field is $\mathbb{Q}/\mathbb{Z}$, and the local Artin map exists. The source uses its own explicit cochains, and it states the local theory for a henselian field that need not be complete. The model case is a finite extension $k$ of $\mathbb{Q}_p$ with $\Gamma = \operatorname{Gal}(\bar{k}/k)$.

### Explicit continuous cochains

Let $G$ be a topological group and $M$ a discrete $G$-module, given as a representation $\rho$ of $G$ over a ring $R$. The source defines the groups $Z^1$, $Z^2$, $B^2$ and $H^2$ by the classical formulas. A continuous map $f : G \to M$ is a 1-cocycle if $f(gh) = f(g) + \rho(g) f(h)$. A continuous map $f : G \times G \to M$ is a 2-cocycle if
$$f(gh, k) = f(g, hk) - f(g, h) + \rho(g) f(h, k)$$
for all $g, h, k$. The 2-coboundaries are the maps $(g, h) \mapsto \rho(g) c(h) - c(gh) + c(g)$ for continuous $c : G \to M$.

**Definition (Continuous $H^2$).** $H^2(G, M)$ is the quotient of the continuous 2-cocycles by the 2-coboundaries of continuous 1-cochains.
Lean: `New.H2` (Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean).

For a profinite $G$ and a discrete $M$, this is the continuous cohomology of Serre, *Galois Cohomology*, Chapter I, §2, in degree 2. The source does not prove that it is the direct limit of the groups $H^2(G/U, M^U)$ of the finite quotients. It does not need this fact as a theorem. It proves instead, directly, that each continuous cocycle is split by an open normal subgroup ([InvariantMap.lean](lean:Lib/ClassField/Local/InvariantMap.lean#L316)).

### Characters and the carry cocycle

**Definition (The group $\mathbb{Q}/\mathbb{Z}$).** `New.QZ` is `AddCircle (1 : ℚ)`, the group $\mathbb{Q}/\mathbb{Z}$, with the discrete topology.
Lean: `New.QZ` (Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean).

**Definition (Continuous characters).** `QZChar G` is the group $Z^1$ of the trivial action on $\mathbb{Q}/\mathbb{Z}$: the continuous homomorphisms $\chi : G \to \mathbb{Q}/\mathbb{Z}$.
Lean: `New.QZChar` (Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean).

Since $\mathbb{Q}/\mathbb{Z}$ is discrete, a continuous character has an open kernel, and for a compact $G$ it has finite image. For each character $\chi$, `QZChar.abelianLift χ` is the induced homomorphism from the topological abelianisation $G^{\mathrm{ab}} = G / \overline{[G, G]}$ to $\mathbb{Q}/\mathbb{Z}$, written multiplicatively.
Lean: `New.QZChar.abelianLift` (Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean).

Classically, the symbol $(\chi, w) = \delta\chi \cup w$ is the cup product of the connecting image $\delta\chi \in H^2(G, \mathbb{Z})$ of $\chi$ with an invariant $w \in M^G$. The source writes the cocycle down. For $a \in \mathbb{Q}/\mathbb{Z}$ let $\{a\} \in [0, 1)$ be its representative. The *carry* of $a, b$ is
$$\operatorname{carry}(a, b) = \lfloor \{a\} + \{b\} \rfloor \in \{0, 1\}.$$
Lean: `New.QZ.carry` (Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean).

**Lemma (The carry is a cocycle).** For $a, b, c \in \mathbb{Q}/\mathbb{Z}$, $\operatorname{carry}(a + b, c) + \operatorname{carry}(a, b) = \operatorname{carry}(a, b + c) + \operatorname{carry}(b, c)$.
Lean: `New.QZ.carry_add_add_carry` (Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean).

*Proof.* In $\mathbb{Q}$, $\operatorname{carry}(a, b) = \{a\} + \{b\} - \{a + b\}$. Substitute this in both sides. Both sides become $\{a\} + \{b\} + \{c\} - \{a + b + c\}$. $\square$

The carry is the standard 2-cocycle of the extension $0 \to \mathbb{Z} \to \mathbb{Q} \to \mathbb{Q}/\mathbb{Z} \to 0$. So $(g, h) \mapsto \operatorname{carry}(\chi g, \chi h)$ represents $\delta \chi$.

**Definition (Cyclic class).** For $\chi \in$ `QZChar G` and an invariant $w \in M^G$, `cyclicClass ρ χ w` is the class in $H^2(G, M)$ of the cocycle $(g, h) \mapsto \operatorname{carry}(\chi g, \chi h) \cdot w$. It is additive in $\chi$ and in $w$.
Lean: `New.cyclicClass` (Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean).

For the Brauer group, $M = \Omega^\times$ is written additively as `DiscreteUnits Ω`, and $w$ is an element of $k^\times$. So `cyclicClass` is the cyclic algebra $(\chi, w)$ of the textbooks, as a cohomology class.

**Example (A quaternion class).** Let $\chi$ have order $2$, with kernel $\operatorname{Gal}(\bar k / k(\sqrt{d}))$. Then $\chi$ takes the values $0$ and $\tfrac12$, and $\operatorname{carry}(\chi g, \chi h) = 1$ exactly when $\chi g = \chi h = \tfrac12$. So the cocycle is $w$ on pairs of elements that both move $\sqrt d$, and $1$ (that is, $0$ additively) on other pairs. Its class is the class of the quaternion algebra $(d, w)$. It is zero exactly when $w$ is a norm from $k(\sqrt d)$.

### Local fields in the source

**Definition (Local Galois setting).** `IsLocalGalois Γ k A` says: $\Gamma$ is the Galois group of $\Omega/k$ (`IsProGalois`), $\Omega$ is algebraically closed of characteristic 0, every element of $\Gamma$ stabilises the valuation subring $A$ of $\Omega$, the ring $A \cap k$ is a discrete valuation ring, and its residue field is finite.
Lean: `New.IsLocalGalois` (Lib/ClassField/Places/GaloisDefs.lean).

The condition that $\Gamma$ stabilises $A$ says that the valuation of $k$ has a unique extension to $\Omega$. This is one of the equivalent forms of the henselian property. Completeness is not asked. So the theory applies to the decomposition field of a place of $\bar{\mathbb{Q}}$, which is henselian but not complete. The source applies it to such fields: for a finite place $v$ of $K$ and a place $A$ over it, the fixed field of the decomposition group of $A$ is a henselian field with Galois group the decomposition group.

**Definition (Normalised order).** `ordRat k A` is an additive map $f : \Omega^\times \to \mathbb{Q}$, chosen by `Classical.epsilon`, with this property: for every uniformiser $\pi$ of $k$, $x^n$ and $\pi^a$ have equal valuation in $A$ exactly when $n f(x) = a$.
Lean: `New.ordRat` (Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean).

So $f$ is the valuation of $A$, normalised by $f(\pi) = 1$. The lemma `valuation_pow_eq_iff_mul_ordRat_eq_of_exists` gives the property when such an $f$ exists. In the local setting the source proves existence.

**Definition (Class of an invariant).** A map $b : \mathbb{Q}/\mathbb{Z} \to H^2(\Gamma, \Omega^\times)$ has the property `IsClassOfInvariant` if $b$ is injective and, for every continuous character $\chi$ that vanishes on the inertia group of $A$, every arithmetic Frobenius $\varphi$ for $q = \#(\text{residue field of } k)$, and every $w \in k^\times$ with $\operatorname{ordRat}(w) = n$,
$$\operatorname{cyclicClass}(\chi, w) = n \cdot b(\chi(\varphi)).$$
The map `Cohomology.classOfInvariant Γ k A` is a map with this property, chosen by `Classical.epsilon`.
Lean: `New.IsClassOfInvariant` (Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean).
Lean: `New.Cohomology.classOfInvariant` (Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean).

So $b$ is the inverse of the invariant map, $b = \operatorname{inv}_k^{-1}$, with the normalisation of Section 2: $\operatorname{inv}_k(\chi, w) = v(w)\chi(\varphi)$ for unramified $\chi$.

**Remark (Formalization).** The source works with the inverse map $b$ and not with $\operatorname{inv}_k$. The reason is that $b$ is easy to write down on the unramified classes: $b(r) = (\chi_r, \pi)$, with $\chi_r$ the unramified character with $\chi_r(\varphi) = r$. The hard part is that $b$ is surjective, that is, that every class is unramified. The property `IsClassOfInvariant` fixes $b$ on the classes $(\chi, w)$ with $\chi$ unramified, and injectivity then fixes $b$ completely. So the choice by `Classical.epsilon` is unique once it exists.

### Tate's index formula

The key count in the local theory is the norm index $[k^\times : N l^\times] = [l : k]$ for a cyclic extension of prime degree. The source gets it from an index formula of Tate.

**Definition (Index of an endomorphism).** For a linear map $f : A \to B$ of abelian groups, `cokerKerIndex f` is the rational number $\#\operatorname{coker} f / \#\ker f$, and it is $0$ if either group is infinite.
Lean: `New.cokerKerIndex` (Lib/ClassField/GaloisCohomology/TateIndexFormula.lean).

The value $0$ is the junk value of Mathlib's `Nat.card` on infinite types. For this reason each statement below asks that one of the indices be nonzero. Write $q(A) = $ `cokerKerIndex` of multiplication by $l$ on $A$, so $q(A) = \#(A/lA) / \#A[l]$.

**Theorem (Tate's index formula).** Let $l$ be prime. Let $B, C$ be abelian groups, $\sigma$ an endomorphism of $B$ with $\sigma^l = 1$, $j : C \to B$ injective and $s : B \to C$, such that $C \xrightarrow{j} B \xrightarrow{\sigma - 1} B \xrightarrow{s} C$ is exact at both inner places and $s \circ j = l$. If $q(C) \neq 0$, then
$$[C : sB]^{\,l - 1} \cdot q(B) = q(C)^l.$$
Lean: `New.Tate.index_formula` (Lib/ClassField/GaloisCohomology/TateIndexFormula.lean).

*Proof.* Let $N = (\sigma - 1)B = \ker s$, and let $t$ be $\sigma - 1$ on $N$. Exactness gives $q(C) = [C : sB] \cdot \operatorname{cokerKerIndex}(t)$. The source shows that on $N$ the map $l$ is $t^{l-1}$ times an automorphism. So $q(N) = \operatorname{cokerKerIndex}(t)^{l - 1}$. Last, $q$ is multiplicative on $0 \to C \to B \to N \to 0$, so $q(B) = q(C) q(N)$. Combine the three equations. $\square$

**Corollary (Norm index in prime degree).** Let $L/K$ be a Galois extension of fields of prime degree $l$. Let $U \leq L^\times$ be stable under $\operatorname{Gal}(L/K)$, and let $V = U \cap K^\times$. Assume that every $z \in L^\times$ with $g z / z \in U$ for all $g$ is in $K^\times U$ (by Hilbert 90 this says $H^1(\operatorname{Gal}(L/K), U) = 0$), and that $q(V) \neq 0$. Then $[V : N_{L/K} U]^{\,l - 1} \cdot q(U) = q(V)^l$.
Lean: `New.tate_index_formula_norm` (Lib/ClassField/GaloisCohomology/TateIndexFormula.lean).

For a local field $k$ of characteristic $0$ and a cyclic extension $l/k$ of prime degree $\ell$, the source computes $q(k^\times) = \ell c$ and $q(l^\times) = \ell c^\ell$, with $c = \#(\mathcal{O}_k / \ell)$. Then the corollary with $U = l^\times$ gives $[k^\times : N l^\times]^{\ell - 1} \cdot \ell c^\ell = (\ell c)^\ell$, so $[k^\times : N l^\times] = \ell$. This is the local first and second inequality at once, in prime degree.

**Lemma (Split classes in prime degree).** Let $V$ be an open normal subgroup of $\Gamma$ of prime index, and let $\beta \neq 0$ be a class split by $V$. Then every class split by $V$ is an integer multiple of $\beta$.
Lean: `New.IsLocalGalois.mem_zmultiples_of_index_prime` (Lib/ClassField/Local/InvariantMap.lean).

*Proof.* Write $V = \ker \psi$ for a character $\psi$. The classes split by $V$ are the symbols $(\psi, y)$ with $y \in k^\times$, and the map $y \mapsto (\psi, y)$ kills the norms. By the corollary, $k^\times / N$ has prime order $[\Gamma : V]$. So the image of a nonzero $\beta$ generates the image. $\square$

### The invariant isomorphism

**Theorem (Invariant map).** In the setting `IsLocalGalois Γ k A`, `classOfInvariant Γ k A` has the property `IsClassOfInvariant`, and it is a bijection $\mathbb{Q}/\mathbb{Z} \to H^2(\Gamma, \Omega^\times)$.
Lean: `New.IsLocalGalois.isClassOfInvariant_classOfInvariant` (Lib/ClassField/Local/InvariantMap.lean).
Lean: `New.IsLocalGalois.classOfInvariant_bijective` (Lib/ClassField/Local/InvariantMap.lean).

*Proof.* For existence, fix a uniformiser $\pi$ and set $b(r) = (\chi_r, \pi)$, where $\chi_r$ is the unramified character with value $r$ at the Frobenius. The unramified computation gives the formula of `IsClassOfInvariant`. For injectivity: if $(\chi_r, \pi) = 0$, then $\pi$ is a norm from the unramified extension cut out by $\chi_r$, and the order of such a norm is a multiple of the degree, so $r = 0$. Then `classOfInvariant` has the property by `Classical.epsilon_spec`. For surjectivity, a continuous cocycle $x$ is split by an open normal subgroup $W$. The class $\beta = b(1/[\Gamma : W])$ is split by $W$, and $n\beta = 0$ only when $[\Gamma : W] \mid n$, by injectivity. The lemma `mem_zmultiples_of_resH2_eq_zero` then shows that every class split by $W$ is a multiple of $\beta$. So $x$ is a multiple of $\beta$. $\square$

**Theorem (Restriction).** Let $V$ be an open subgroup of $\Gamma$ with fixed field $k_V$. Restriction to $V$ sends $b_k(r)$ to $b_{k_V}([\Gamma : V] \cdot r)$.
Lean: `New.Cohomology.resH2_classOfInvariant` (Lib/ClassField/Local/InvariantMap.lean).

This is the classical rule $\operatorname{inv}_{k'} \circ \operatorname{res} = [k' : k] \operatorname{inv}_k$ of Serre, *Local Fields*, Chapter XIII, §3. The source proves it in the form "a map of local fields with ramification index $e$ and residue degree $f$ multiplies the invariant by $ef$", and uses $ef = [\Gamma : V]$.

### The local Artin map in the source

**Definition (Local Artin property).** A homomorphism $f : L^\times \to \Gamma^{\mathrm{ab}}$ has the property `IsLocalArtin Γ k A` if, for every continuous character $\chi$ of $\Gamma$ and every $x \in L^\times$,
$$\operatorname{classOfInvariant}(\chi(f(x))) = -\operatorname{cyclicClass}(\chi, x).$$
Lean: `New.IsLocalArtin` (Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean).

In textbook terms, $\chi(f(x)) = -\operatorname{inv}(\chi, x)$. This is the inverse of the map of Section 2. The next lemma makes the sign concrete.

**Lemma (Uniformisers and Frobenius).** Let $F$ have the property `IsLocalArtin Γ k A` in the setting `IsLocalGalois Γ k A`, and let $\pi$ be a uniformiser of $k$. Then $F(\pi)$ is the class of $\varphi^{-1}$ for some arithmetic Frobenius $\varphi$.
Lean: `New.IsLocalArtin.exists_frob_of_isUniformiser` (Lib/ClassField/Local/ArtinMap.lean).

*Proof.* For an unramified $\chi$, $\operatorname{cyclicClass}(\chi, \pi) = b(\chi(\varphi))$, since $\pi$ has order $1$. So $\chi(F\pi) = -\chi(\varphi) = \chi(\varphi^{-1})$. Characters separate a closed subgroup from a point outside it, so $\varphi^{-1} / F(\pi)$ lies in the image of the inertia group. Replace $\varphi$ by $\varphi \tau$ for an element $\tau$ of inertia. $\square$

So the source uses the geometric convention: uniformisers go to geometric Frobenius elements.

**Definition (Local Artin map at a prime).** Let $v$ be a finite place of a number field $K$ and $A$ a place of $\Omega$. Then `localArtin Γ A v` is a homomorphism $K_v^\times \to D_A^{\mathrm{ab}}$, with $D_A$ the decomposition group, chosen by `Classical.epsilon` so that its restriction to $K^\times$ has the property `IsLocalArtin` over the fixed field of $D_A$.
Lean: `New.localArtin` (Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean).

**Theorem (The local Artin map exists).** Let $A$ lie over $v$, and let $A$ come from an embedding of $\Omega$ and of $K_v$ in $\bar{\mathbb{Q}}_p$ (the hypothesis `IsCompletionEmb`). Then $f = $ `localArtin Γ A v` has the property `IsLocalArtin` (a) on $K_v^\times$, with the invariant of $K_v$ read in $\bar{\mathbb{Q}}_p$, and (b) on $K^\times$, with the invariant of the fixed field of $D_A$.
Lean: `New.IsPlaceOver.isLocalArtin_localArtin` (Lib/ClassField/Local/ArtinMap.lean).

*Proof.* For $x \in K_v^\times$, the map $\chi \mapsto -\operatorname{inv}(\chi, x)$ is a homomorphism from the characters of $D_A$ to $\mathbb{Q}/\mathbb{Z}$, additive in $x$, with $\operatorname{inv}$ the invariant of $K_v$ read in $\bar{\mathbb{Q}}_p$. By a duality lemma for profinite groups (`New.QZChar.exists_hom_abelianLift_eq`), there is a homomorphism $f : K_v^\times \to D_A^{\mathrm{ab}}$ with $\chi(f(x)) = -\operatorname{inv}(\chi, x)$. This is property (a). The decomposition field and $K_v$ have the same Galois group, and the embedding in $\bar{\mathbb{Q}}_p$ matches their invariants. So $f$ has property (b) on $K^\times$. Then `localArtin` has property (b) by `Classical.epsilon_spec`. Two continuous maps with property (b) agree on $K^\times$, by injectivity of $b$, and $K^\times$ is dense in $K_v^\times$. So `localArtin` $= f$, and it has property (a) too. $\square$

**Remark (Formalization).** The local theory is proved here for henselian fields in the axioms of `IsLocalGalois`. The source does not prove local reciprocity in the textbook form $k^\times / N l^\times \cong \operatorname{Gal}(l/k)$ for every abelian $l/k$. It proves what the global theory uses: the invariant isomorphism, its behaviour under restriction, the norm index in prime degree and the local Artin map as a map characterised by invariants. The two files of `Lib/ClassField/Local` do not state the local existence theorem. The global existence theorem of Section 8 does not use it.
