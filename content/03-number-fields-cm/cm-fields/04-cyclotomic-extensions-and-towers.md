---
title: Cyclotomic extensions of K and the towers
lean:
  - Lib/ClassField/Places/DecompositionCyclotomic.lean
  - Lib/ClassField/Places/ProfiniteGalois.lean
  - Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean
decls:
  - New.Ω
  - New.fixedFieldOf
  - New.finrank_fixedFieldOf
  - New.fixingSubgroup_fixedFieldOf
  - New.cyclotomicCharMod
  - New.cyclotomicCharMod_eq_iff
  - New.cycloGalGroup
  - New.cycloField
  - New.cyclotomicCharMod_surjective
status: drafted
drafted_by: writer@claude-opus-5-5
---

## Cyclotomic extensions of K and the towers

The field $E$ of the argument is a cyclotomic extension of $K$. This section recalls the classical theory of cyclotomic extensions, shows why $\Phi_{q_1}$ stays irreducible over $K$, and lists the towers of fields that the proof uses. It then gives the form of the source: a fixed algebraic closure $\Omega$ of $\mathbb{Q}$, its Galois group with the Krull topology, the cyclotomic character, and the cyclotomic fields as fixed fields.

### The classical theory

Let $n \ge 1$ and let $\zeta_n$ be a primitive $n$-th root of unity. The cyclotomic polynomial $\Phi_n$ is irreducible over $\mathbb{Q}$, so $[\mathbb{Q}(\zeta_n) : \mathbb{Q}] = \varphi(n)$, and $a \mapsto (\zeta_n \mapsto \zeta_n^a)$ is an isomorphism $(\mathbb{Z}/n)^\times \cong \mathrm{Gal}(\mathbb{Q}(\zeta_n)/\mathbb{Q})$ (Neukirch, Ch. I, §10; Washington, Ch. 2). A prime $p \nmid n$ is unramified in $\mathbb{Q}(\zeta_n)$, its Frobenius is $\zeta_n \mapsto \zeta_n^p$, and its residue degree is the order of $p$ modulo $n$ (Neukirch, Ch. I, Prop. 10.3). The discriminant of $\mathbb{Q}(\zeta_n)$ is given in Washington, Prop. 2.7.

Over a number field $F$ in place of $\mathbb{Q}$, the polynomial $\Phi_n$ can factor. The extension $F(\zeta_n)/F$ is abelian, and its Galois group is the image of $\mathrm{Gal}(F(\zeta_n)/F) \to (\mathbb{Z}/n)^\times$, a subgroup of index $[F \cap \mathbb{Q}(\zeta_n) : \mathbb{Q}]$. For $F = K$ and $\gcd(n, d) = 1$, the intersection $K \cap \mathbb{Q}(\zeta_n)$ is $\mathbb{Q}$. Indeed, it is a subfield of $K$, so it is $\mathbb{Q}$ or $K$. The prime $d$ ramifies in $K$ and is unramified in $\mathbb{Q}(\zeta_n)$, so it is not $K$. So $\Phi_n$ is irreducible over $K$ and $[K(\zeta_n) : K] = \varphi(n)$.

The source proves this for $n = q_1$ by a degree count, without ramification. It embeds $K$ in $M = \mathbb{Q}(\zeta_d)$ by the Gauss sum of Section 2, and it shows that $M(\zeta_{q_1})$ has degree at least $\varphi(d) \varphi(q_1)$ over $\mathbb{Q}$, since it contains a primitive root of order $q_1 d$ and $\gcd(q_1, d) = 1$. So $\Phi_{q_1}$ is irreducible over $M$, hence over $K$. The statement is `New.Parameters.irreducible_cyclotomic`, in [the field E](/chapter/fields-places-twists/).

### The towers

The proof uses five towers of fields. The first two are classical, and the last three are built in the source.

1. $\mathbb{Q} \subset K \subset E \subset \mathbb{Q}(\zeta_{q_1 d})$. The field $E = K(\zeta_{q_1})$ embeds in $\mathbb{Q}(\zeta_{q_1 d})$, since $K \subset \mathbb{Q}(\zeta_d)$. So $E$ is abelian over $\mathbb{Q}$, and $\mathrm{Gal}(E/\mathbb{Q}) \cong \{\pm 1\} \times (\mathbb{Z}/q_1)^\times$. The embedding is `New.Parameters.toCycloField`, in [the field E](/chapter/fields-places-twists/).
2. $E^+ \subset E$. Since $E$ is abelian over $\mathbb{Q}$ and totally complex, it is CM by `NumberField.IsCMField.of_isAbelianGalois` (Mathlib), an instance. So $E^+$ is the fixed field of complex conjugation, of degree $\varphi(q_1)$ over $\mathbb{Q}$.
3. The family $(E_s)_{s \ge 0}$, one field for each level $s$. Here $q_1(s) = q_0 \cdot 3^{c(s)} 2^s$.
4. Fields $K \subset L \subset \bar{\mathbb{Q}}$ with $\mathrm{Gal}(\bar{\mathbb{Q}}/L)$ an open subgroup of $\mathrm{Gal}(\bar{\mathbb{Q}}/K)$. The ramification of places in such towers is in Section 5.
5. Fields $E \subset E[X]/(P)$ and fixed fields of automorphisms, in the base change steps. They are CM by Section 3.

**Remark (Formalization).** In the third tower, $c(s)$ is nondecreasing in $s$ and $2^s \mid 2^{s+1}$, so $\mathrm{towerDeg}(s) \mid \mathrm{towerDeg}(s+1)$ and $q_1(s) \mid q_1(s+1)$. So classically $E_s \subset E_{s+1}$. The source does not use this. It defines each $E_s$ as a separate type, `CyclotomicField (q₁ s) K`, and this book has found no map from $E_s$ to $E_{s+1}$ in it. Every statement about $E$ is made for one fixed $s$. The level $s$ enters the argument only through the size of $q_1$ and the number $f = \mathrm{towerDeg}(s) \varphi(q_0)$ of infinite places.

### The fixed algebraic closure

The source puts number fields that must be compared inside one algebraic closure of $\mathbb{Q}$.

**Definition (The algebraic closure Ω).** The field $\Omega$ is Mathlib's algebraic closure `AlgebraicClosure ℚ` of $\mathbb{Q}$.

Lean: `New.Ω` (Lib/ClassField/Places/GaloisDefs.lean).

**Remark (Formalization).** The source declares an instance that $\Omega$ is an algebraic closure of every field $F$ of characteristic $0$ with an $F$-algebra structure on $\Omega$ (Lib/ClassField/Places/ProfiniteGalois.lean, the first instance of the file). This is true: $\Omega$ is algebraically closed and algebraic over $\mathbb{Q}$, hence over $F$. The instance is global, so it applies to every algebra structure in every file that imports it. The source also defines `New.Ω.fieldEmb`, an embedding of a number field into $\Omega$ chosen by `Classical.ofNonempty`. The fields $E$ and $E[X]/(P)$ are not subfields of $\Omega$, so a statement over $\Omega$ about them depends on a chosen embedding or an algebra structure given as a hypothesis.

For a field $F$ with an algebra structure on $\Omega$, the group $\Gamma = \mathrm{Gal}(\Omega / F)$ is profinite with the Krull topology. In the source, the class `New.IsProGalois Γ F Ω` asks that $\Gamma$ act on $\Omega$ as its Galois group over $F$, be compact, totally disconnected and topological, and that the stabiliser of every element be open. The Galois group with the Krull topology is an instance of the class. The class allows an abstract group $\Gamma$, so that a decomposition group, which is a subgroup, can serve as the Galois group of its fixed field.

**Definition (Fixed field).** Let $\Gamma$ satisfy `IsProGalois Γ F Ω`, and let $H$ be a subgroup of $\Gamma$. The fixed field of $H$ is the intermediate field of $\Omega/F$ of the elements fixed by every $h \in H$.

Lean: `New.fixedFieldOf` (Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean).

**Theorem.** Let $\Gamma$ satisfy `IsProGalois Γ F Ω`, and let $H$ be a closed subgroup of $\Gamma$. Then the subgroup of $\Gamma$ that fixes the fixed field of $H$ pointwise is $H$, and $[\mathrm{Fix}(H) : F]$ is the index of $H$ in $\Gamma$.

Lean: `New.fixingSubgroup_fixedFieldOf`, `New.finrank_fixedFieldOf` (Lib/ClassField/Places/ProfiniteGalois.lean).

This is the fundamental theorem of infinite Galois theory (Neukirch, Ch. IV, §1). It is stated for an abstract $\Gamma$, and the source proves it by transport from Mathlib's version for $\mathrm{Gal}(\Omega/F)$.

**Remark (Formalization).** If $H$ has infinite index, then the fixed field has infinite degree. Both sides of the equation are then $0$, by the conventions of Mathlib: `Module.finrank` is $0$ for an infinite dimensional space, and `Subgroup.index` is $0$ for an infinite index. So the statement holds with no hypothesis on the index, but it carries information only for open $H$, for which the index is finite. For open $H$ the source has instances that the fixed field is finite over $F$ and is a number field when $F$ is one.

### The cyclotomic character and the cyclotomic fields

**Definition (Cyclotomic character).** Let $\Gamma$ act on a field $\Omega$ with all $N$-th roots of unity, $N \ne 0$. The cyclotomic character modulo $N$ is the homomorphism $\chi_N : \Gamma \to (\mathbb{Z}/N)^\times$ with $g \zeta = \zeta^{\chi_N(g)}$ for every $N$-th root of unity $\zeta$.

Lean: `New.cyclotomicCharMod`, `New.cyclotomicCharMod_eq_iff` (Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean, Lib/ClassField/Places/DecompositionCyclotomic.lean).

The source defines $\chi_N$ as Mathlib's `modularCyclotomicCharacter` (Mathlib) composed with the action of $\Gamma$ by ring automorphisms. The lemma `New.cyclotomicCharMod_eq_iff` is the characterisation for $\Omega$ algebraically closed of characteristic $0$ and $a \in \mathbb{N}$: $\chi_N(g) = a$ in $\mathbb{Z}/N$ if and only if $g \zeta = \zeta^a$ for every $\zeta$ with $\zeta^N = 1$.

**Definition (Cyclotomic field in Ω).** For $N \ne 0$, let $\Gamma_N \subset \mathrm{Gal}(\Omega/\mathbb{Q})$ be the kernel of $\chi_N$. The cyclotomic field $\mathbb{Q}(\zeta_N) \subset \Omega$ is the fixed field of $\Gamma_N$.

Lean: `New.cycloGalGroup`, `New.cycloField` (Lib/ClassField/Places/DecompositionCyclotomic.lean).

**Theorem.** For $N \ne 0$, the field `New.cycloField N` is a cyclotomic extension of $\mathbb{Q}$ generated by the $N$-th roots of unity, and the cyclotomic character $\chi_N$ of $\mathrm{Gal}(\Omega/\mathbb{Q})$ is surjective.

Lean: `New.cyclotomicCharMod_surjective` (Lib/ClassField/Places/DecompositionCyclotomic.lean).

*Proof.* An element of $\mathrm{Gal}(\Omega/\mathbb{Q})$ fixes all $N$-th roots of unity if and only if $\chi_N$ is $1$ at it. So $\Gamma_N$ is the group that fixes the field generated by the $N$-th roots of unity, and by the fundamental theorem the fixed field of $\Gamma_N$ is this field. Its degree over $\mathbb{Q}$ is $\varphi(N)$, by the irreducibility of $\Phi_N$. So $\Gamma_N$ has index $\varphi(N)$ in $\mathrm{Gal}(\Omega/\mathbb{Q})$. The image of $\chi_N$ is isomorphic to the quotient by $\Gamma_N$, so it has $\varphi(N)$ elements, and it is all of $(\mathbb{Z}/N)^\times$. $\square$

**Remark (Formalization).** The first claim of the theorem is an instance of the source, `IsCyclotomicExtension {N} ℚ (cycloField N)`, with no name. With it, every result of Mathlib on cyclotomic extensions of $\mathbb{Q}$ applies to the subfield `New.cycloField N` of $\Omega$, and the source uses this for $N = d$ in the proof that $\Phi_{q_1}$ is irreducible over $K$. The field $\mathbb{Q}(\zeta_{q_1 d})$ that receives $E$ in the first tower is also `New.cycloField (q₁ * d)`. So $E$ maps to a subfield of $\Omega$, but only through the chosen map `New.Parameters.toCycloField`.

The value of $\chi_N$ at a Frobenius element is the norm of the prime, as in the classical theory. The source states this in Section 5, after it has defined Frobenius elements at places of $\Omega$.
