---
title: Finite ideles and Galois groups
lean:
  - Lib/Adelic/Adeles/Basic.lean
  - Lib/ClassField/Places/Ideles.lean
  - Lib/ClassField/Places/GaloisDefs.lean
  - Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean
decls:
  - New.FinPlace.q
  - New.uniformizer
  - New.principalIdele
  - New.locIdele
  - New.ideleAt
  - New.idelesUnitOff
  - New.IsTotallyPositive
  - New.finiteIndex_idele_subgroup_of_isOpen
  - New.exists_idele_classGroup_hom
  - New.IsProGalois
  - New.IsComplexConj
  - New.IsFrob
  - New.inertiaGroup
  - New.IsPlaceOver
  - New.placeOver
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Finite ideles and Galois groups

This section fixes the objects of the source: the finite ideles, the Galois group of an algebraic closure, the places of the closure, and Frobenius elements. The chapter [CM fields and places](/chapter/cm-fields/) explains the number fields, the infinite places and the embeddings in more detail. This section gives only what the class field theory needs.

### Finite places and finite ideles

Let $K$ be a number field. The source writes `FinPlace K` for the set of nonzero prime ideals of $\mathcal{O}_K$, the *finite places*. It writes $K_v$ for the completion `v.adicCompletion K` (also written `LocField v`), and `𝔸f K` for the finite adele ring of Mathlib, `FiniteAdeleRing (𝓞 K) K`. The finite ideles are the units $(\mathbb{A}_{K,f})^\times$ of this ring. Mathlib gives the units of a topological ring the topology for which $a \mapsto (a, a^{-1})$ is an embedding. On the finite ideles this is the restricted product topology of Section 2, so $(\mathbb{A}_{K,f})^\times = J_{K,f}$ as topological groups.

**Definition (Norm of a finite place).** For a finite place $v$ of $K$, $q_v$ is the absolute norm of the prime ideal $v$, the order of $\mathcal{O}_K / v$.
Lean: `New.FinPlace.q` (Lib/Adelic/Adeles/Basic.lean).

The value is a natural number, and the source proves $1 < q_v$. So no junk value occurs here.

**Definition (Uniformiser).** For a finite place $v$, $\varpi_v$ is a chosen unit of $K_v$ of valuation $e^{-1}$ in the multiplicative valuation of Mathlib, that is, of order $1$.
Lean: `New.uniformizer` (Lib/Adelic/Adeles/Basic.lean).

**Remark (Formalization).** The uniformiser is chosen by `Exists.choose` from the surjectivity of the valuation. So $\varpi_v$ is a specific element, but the source does not say which one. Each statement that uses it, for example the Euler factors $1 - \psi(\varpi_v) q_v^{-s}$ of Section 5, is true for every uniformiser when $\psi$ is unramified at $v$. At a ramified place the value $\psi(\varpi_v)$ depends on the choice. Section 5 explains where this matters.

The source has four maps between $K^\times$, the local fields and the finite ideles.

**Definition (Principal, local and component maps).** The map `principalIdele` is the diagonal homomorphism $K^\times \to (\mathbb{A}_{K,f})^\times$. For a finite place $v$, `locIdele v` sends $x \in K_v^\times$ to the idele with component $x$ at $v$ and $1$ at every other place, and `ideleAt v` sends an idele to its component at $v$. For a set $S$ of finite places, `idelesUnitOff S` is the subgroup of ideles whose components are units at every $v \notin S$.
Lean: `New.principalIdele` (Lib/ClassField/Places/Ideles.lean).
Lean: `New.locIdele` (Lib/ClassField/Places/Ideles.lean).
Lean: `New.ideleAt` (Lib/ClassField/Places/Ideles.lean).
Lean: `New.idelesUnitOff` (Lib/ClassField/Places/Ideles.lean).

So `idelesUnitOff ∅` is $\prod_v \mathcal{O}_v^\times = \hat{\mathcal{O}}_K^\times$. The source proves that it is open and compact.

### Total positivity

**Definition (Totally positive).** An element $x \in K$ is *totally positive* if $\varphi(x) > 0$ for every ring homomorphism $\varphi : K \to \mathbb{R}$.
Lean: `New.IsTotallyPositive` (Lib/ClassField/Places/Ideles.lean).

If $K$ has no real embedding, every $x$ is totally positive, $0$ included. In the source the condition is always applied to a unit $x \in K^\times$. The subgroup of principal ideles of totally positive elements plays the role of $K^\times K_\infty^{\times,0}$ in the finite idele form of Section 2.

**Lemma (Open subgroups have finite index).** Let $H$ be an open subgroup of $(\mathbb{A}_{K,f})^\times$ that contains the principal idele of every totally positive $x \in K^\times$. Then $H$ has finite index.
Lean: `New.finiteIndex_idele_subgroup_of_isOpen` (Lib/ClassField/Places/Ideles.lean).

*Proof.* Let $P$ be the group of principal ideles and $U = \hat{\mathcal{O}}_K^\times$. The proof climbs from $H$ to $H P$, to $H P U$, and to the whole group. First, the preimage of $H$ in $K^\times$ contains the kernel of the sign map $K^\times \to \{\pm 1\}^{r_1}$, so it has finite index in $K^\times$, and $[HP : H]$ is finite. Second, $H$ is open, so it contains $\prod_{v \in S} (1 + \mathfrak{p}_v^{n}) \times \prod_{v \notin S} \mathcal{O}_v^\times$ for a finite $S$ and some $n$. This group has finite index in the compact group $U$, so $[HPU : HP]$ is finite. Third, $(\mathbb{A}_{K,f})^\times / P U$ is the class group (the next lemma), which is finite. $\square$

**Lemma (Ideles and the class group).** There is a homomorphism $c : (\mathbb{A}_{K,f})^\times \to \operatorname{Cl}_K$ whose kernel is generated by the principal ideles and $\hat{\mathcal{O}}_K^\times$.
Lean: `New.exists_idele_classGroup_hom` (Lib/ClassField/Places/Ideles.lean).

*Proof.* Send an idele $(a_v)$ to the class of its divisor $\prod_v v^{\operatorname{ord}_v(a_v)}$. The divisor is trivial exactly on $\hat{\mathcal{O}}_K^\times$. The class is trivial exactly when the divisor is principal, that is, the divisor of a principal idele. $\square$

The lemma is an existence statement, so the source does not fix one map $c$. Every use needs only the kernel.

### The Galois group

The source fixes one algebraic closure, $\Omega = $ `New.Ω`, the type `AlgebraicClosure ℚ` of Mathlib. Every number field of the main argument is given an algebra map to $\Omega$. A Galois group is an abstract topological group $\Gamma$ that acts on $\Omega$, with a property that says that $\Gamma$ is the Galois group.

**Definition (Profinite Galois group).** Let $K \subseteq \Omega$ be a field and $\Gamma$ a topological group that acts on $\Omega$. The class `IsProGalois Γ K Ω` says that $\Gamma$ acts as the Galois group of $\Omega / K$ (Mathlib's `IsGaloisGroup`), that $\Omega/K$ is Galois, that $\Gamma$ is a compact, totally disconnected topological group, and that the stabiliser of each $x \in \Omega$ is open.
Lean: `New.IsProGalois` (Lib/ClassField/Places/GaloisDefs.lean).

The last condition makes the topology the Krull topology. The main example is $\Gamma = \operatorname{Gal}(\Omega/K)$ with the Krull topology. The abstract form lets the source apply the same lemmas to the decomposition groups and to the open subgroups $\operatorname{Gal}(\Omega/L)$ for $K \subseteq L$.

**Definition (Complex conjugation).** An element $c \in \Gamma$ is a *complex conjugation* if there is a ring map $j : \Omega \to \mathbb{C}$ with $j(c x) = \overline{j(x)}$ for every $x \in \Omega$.
Lean: `New.IsComplexConj` (Lib/ClassField/Places/GaloisDefs.lean).

The identity is not a complex conjugation, since $j(\sqrt{-1})$ is not real. The source proves that $c^2 = 1$, and that a totally complex $K$ has no complex conjugation in its Galois group ([AlbertBrauerHasseNoether.lean](lean:Lib/ClassField/Global/AlbertBrauerHasseNoether.lean#L140)). If $K$ has a real embedding $\sigma$, then every $j$ that extends $\sigma$ gives a complex conjugation in $\operatorname{Gal}(\Omega/K)$.

### Places of the closure and Frobenius elements

A place of $\Omega$ is a valuation subring $A \subseteq \Omega$. The source writes `ClosurePlace` for the type of valuation subrings of `New.Ω`. The *decomposition group* `decompGroup Γ A` is the stabiliser of $A$ in $\Gamma$.

**Definition (Place over a prime).** The valuation subring $A$ of $\Omega$ lies over the finite place $v$ of $K$ if, for each $x \in \mathcal{O}_K$, $x$ is in the maximal ideal of $A$ exactly when $x \in v$.
Lean: `New.IsPlaceOver` (Lib/ClassField/Places/GaloisDefs.lean).

**Definition (Frobenius element).** Let $q$ be a natural number. An element $\sigma \in \Gamma$ is a $q$-*Frobenius* at $A$ if $\sigma$ stabilises $A$ and $\sigma x - x^q$ lies in the maximal ideal of $A$ for every $x \in A$.
Lean: `New.IsFrob` (Lib/ClassField/Places/GaloisDefs.lean).

**Definition (Inertia group).** The *inertia group* of $A$ is the set of $1$-Frobenius elements: the $\sigma$ that stabilise $A$ and act trivially on the residue field of $A$.
Lean: `New.inertiaGroup` (Lib/ClassField/Places/GaloisDefs.lean).

So a Frobenius element in the sense of the source is an *arithmetic* Frobenius: it acts as $x \mapsto x^q$ on the residue field. It is not unique. Two $q$-Frobenius elements at $A$ differ by an element of the inertia group. The definition does not ask that $q$ be the order of the residue field of $K$. Each statement that uses it gives the value of $q$, usually $q = q_v$.

**Definition (Chosen place).** For a finite place $v$ of $K$, `placeOver v` is a valuation subring of $\Omega$ chosen by `Classical.epsilon` with the property that it lies over $v$.
Lean: `New.placeOver` (Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean).

**Remark (Formalization).** A definition by `Classical.epsilon` is total: if no object has the property, the definition still gives an object, and nothing is known about it. So each such definition comes with a lemma that says that the chosen object has its property when some object has it. For `placeOver` the lemma is `isPlaceOver_placeOver_of_exists`, and the source proves that a place over $v$ exists, so `placeOver v` does lie over $v$ ([ValuationSubrings.lean](lean:Lib/ClassField/Places/ValuationSubrings.lean#L193), `New.FinPlace.isPlaceOver_placeOver`). This pattern occurs five times in this chapter: `placeOver`, the normalised order `ordRat`, the invariant map `classOfInvariant`, the local Artin map `localArtin` and the global Artin map `artinMap`. For each, this chapter names the lemma that removes the hypothesis of existence.

**Example (The place over $p$ in $\mathbb{Q}$).** Let $K = \mathbb{Q}$ and $v = (p)$. A valuation subring $A$ of $\Omega$ over $p$ is the valuation ring of the restriction to $\Omega$ of the valuation of $\bar{\mathbb{Q}}_p$, for some embedding $\Omega \to \bar{\mathbb{Q}}_p$. Its decomposition group is the image of $\operatorname{Gal}(\bar{\mathbb{Q}}_p / \mathbb{Q}_p)$. An element $\sigma$ is a $p$-Frobenius at $A$ exactly when it acts on the residue field $\bar{\mathbb{F}}_p$ of $A$ as $x \mapsto x^p$. On $\mathbb{Q}(\zeta_m)$ with $p \nmid m$, such a $\sigma$ acts as $\zeta_m \mapsto \zeta_m^p$.
