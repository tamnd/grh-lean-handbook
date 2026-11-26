---
title: Finite places, decomposition and Frobenius
lean:
  - Lib/Adelic/Adeles/Basic.lean
  - Lib/ClassField/Places/GaloisDefs.lean
  - Lib/ClassField/Places/ValuationSubrings.lean
  - Lib/ClassField/Places/DecompositionCompletion.lean
  - Lib/ClassField/Places/DecompositionCyclotomic.lean
decls:
  - New.FinPlace
  - New.FinPlace.q
  - New.FinPlace.one_lt_q
  - New.FinPlace.IsSplit
  - New.mem_star_place
  - New.placeOfEmb
  - New.mem_placeOfEmb
  - New.placeOfEmb_comp_star
  - New.FinPlace.ncard_mul_ramificationIdx_mul_inertiaDeg
  - New.IsPlaceOver
  - New.placeOver
  - New.decompGroup
  - New.IsFrob
  - New.inertiaGroup
  - New.IsFrob.inv_mul_mem_inertiaGroup
  - New.IsPlaceOver.isLocalGalois_and_residueCard_eq_and_isUniformiser
  - New.IsPlaceOver.exists_isFrob
  - New.IsPlaceOver.ramification_in_tower
  - New.IsFrob.cyclotomicCharMod_eq
  - New.IsFrob.mem_ker_cyclotomicCharMod_iff
status: drafted
drafted_by: writer@claude-opus-5-5
---

## Finite places, decomposition and Frobenius

This section gives the classical theory of the finite places of a number field: prime ideals, the formula $\sum e_i f_i = n$, decomposition and inertia groups, and Frobenius elements. It then gives the two forms of the source. A finite place of a number field is a nonzero prime ideal of its ring of integers, as in Mathlib. A place of the algebraic closure $\Omega$ is a valuation subring of $\Omega$, and decomposition groups, inertia groups and Frobenius elements are defined from it.

### The classical theory

Let $F$ be a number field with ring of integers $\mathcal{O}_F$. A finite place of $F$ is a nonzero prime ideal $\mathfrak{p}$ of $\mathcal{O}_F$. Its norm $N\mathfrak{p} = |\mathcal{O}_F/\mathfrak{p}|$ is a power of the prime $p$ below it, so $N\mathfrak{p} \ge 2$.

Let $L/F$ be an extension of degree $n$ and $\mathfrak{p} \mathcal{O}_L = \mathfrak{P}_1^{e_1} \cdots \mathfrak{P}_r^{e_r}$, with residue degrees $f_i$. Then $\sum_i e_i f_i = n$ (Neukirch, Ch. I, Prop. 8.2). If $L/F$ is Galois, then $\mathrm{Gal}(L/F)$ acts transitively on the $\mathfrak{P}_i$, all $e_i$ are equal to one $e$ and all $f_i$ to one $f$, and $r e f = n$ (Neukirch, Ch. I, §9).

For $L/F$ Galois and $\mathfrak{P}$ over $\mathfrak{p}$, the decomposition group $D_\mathfrak{P}$ is the stabiliser of $\mathfrak{P}$, and the inertia group $I_\mathfrak{P}$ is the kernel of $D_\mathfrak{P} \to \mathrm{Gal}(\kappa(\mathfrak{P})/\kappa(\mathfrak{p}))$. This map is surjective, and $|D_\mathfrak{P}| = e f$, $|I_\mathfrak{P}| = e$ (Neukirch, Ch. I, §9). A Frobenius element at $\mathfrak{P}$ is a $\sigma \in D_\mathfrak{P}$ with $\sigma x \equiv x^{N\mathfrak{p}} \bmod \mathfrak{P}$ for all $x \in \mathcal{O}_L$. It exists, and it is unique modulo $I_\mathfrak{P}$. For $L = F(\zeta_N)$ and $\mathfrak{p} \nmid N$, the Frobenius acts on roots of unity by $\zeta \mapsto \zeta^{N\mathfrak{p}}$. Only finitely many primes ramify in a finite extension. For an infinite Galois extension, such as $\bar{\mathbb{Q}}/F$, the same theory holds with the Krull topology, and the groups are closed subgroups (Neukirch, Ch. IV, §1, for the topology; Serre, Local Fields, Ch. I, §7, for the finite case).

For a CM field $E$, complex conjugation $c$ acts on the primes of $E$. A prime $\mathfrak{p}$ of $E$ is split over $E^+$ if $c\mathfrak{p} \ne \mathfrak{p}$. Then $\mathfrak{p} \cap E^+$ splits into $\mathfrak{p}$ and $c\mathfrak{p}$.

### Finite places of a number field

**Definition (Finite place).** A finite place of a number field $E$ is a height one prime of $\mathcal{O}_E$, that is, a nonzero prime ideal. Its norm $q_w$ is the absolute norm of the ideal.

Lean: `New.FinPlace`, `New.FinPlace.q` (Lib/Adelic/Adeles/Basic.lean).

**Lemma.** For every finite place $w$, $q_w > 1$.

Lean: `New.FinPlace.one_lt_q` (Lib/Adelic/Adeles/Basic.lean).

**Definition (Conjugate place and split place).** Let $E$ be a CM field. The conjugate $\bar w$ of a finite place $w$ is the preimage of $w$ under complex conjugation of $\mathcal{O}_E$. So $x \in \bar w$ if and only if $\bar x \in w$. The place $w$ is split if $\bar w \ne w$.

Lean: `New.mem_star_place`, `New.FinPlace.IsSplit` (Lib/Adelic/Adeles/Basic.lean).

The conjugation of $\mathcal{O}_E$ is the restriction of `NumberField.IsCMField.ringOfIntegersComplexConj` (Mathlib), and so it comes from `NumberField.IsCMField.complexConj` (Mathlib). Section 3 gives its definition by `choose`. The source makes $\mathcal{O}_E$ a star ring and the finite places an involutive star type with this conjugation.

**Theorem.** Let $L/K$ be a Galois extension of number fields and $w$ a finite place of $L$. Let $r$ be the number of places of $L$ over the place of $K$ below $w$, and let $e$, $f$ be the ramification index and inertia degree of $w$. Then $r e f = [L : K]$.

Lean: `New.FinPlace.ncard_mul_ramificationIdx_mul_inertiaDeg` (Lib/ClassField/Places/ValuationSubrings.lean).

The source proves this from Mathlib's formula for the prime ideals over a prime. The number $r$ is the cardinality `Set.ncard` of a set. Its value is $0$ for an infinite set, but the set is finite here, and the equation shows it.

### Places from embeddings

The base change and level raising steps put a number field $E$ inside a $p$-adic field. An embedding $\sigma : E \to F$ into a field $F$ over $\mathbb{Q}_p$ with an ultrametric norm gives a place of $E$.

**Definition (Place of an embedding).** Let $\sigma : E \to F$ be a ring homomorphism, where $F$ is a normed field over $\mathbb{Q}_p$ with an ultrametric norm. The place $w_\sigma$ is the centre on $\mathcal{O}_E$ of the valuation ring $\{x \in E : \|\sigma x\| \le 1\}$. So an integer $x$ of $E$ is in $w_\sigma$ if and only if $\|\sigma x\| < 1$.

Lean: `New.placeOfEmb`, `New.mem_placeOfEmb` (Lib/ClassField/Places/ValuationSubrings.lean).

**Proposition.** Let $E$ be a CM field and $c$ its complex conjugation. Then $w_{\sigma \circ c} = \overline{w_\sigma}$.

Lean: `New.placeOfEmb_comp_star` (Lib/ClassField/Places/ValuationSubrings.lean).

*Proof.* For $x \in \mathcal{O}_E$, $x \in w_{\sigma \circ c}$ if and only if $\|\sigma(\bar x)\| < 1$, if and only if $\bar x \in w_\sigma$, if and only if $x \in \overline{w_\sigma}$. $\square$

**Remark (Formalization).** The source marks `New.placeOfEmb` as irreducible, so that a proof uses only `New.mem_placeOfEmb` and the valuation lemmas, not the construction. The source also extends $\sigma$ to the finite adeles through a completion. This extension is `New.adeleExtension`, and the place it uses, `New.placeOfEmbExtension`, is chosen.

### Places of the algebraic closure

The source defines the decomposition and inertia groups at a place of $\Omega$, not at a prime of a finite extension. A place of $\Omega$ over a prime $v$ of $K$ corresponds classically to a compatible system of primes over $v$ in all finite subextensions.

**Definition (Place over a prime).** Let $\Omega$ be a field over a number field $K$, $A$ a valuation subring of $\Omega$, and $v$ a finite place of $K$. Then $A$ lies over $v$ if, for every $x \in \mathcal{O}_K$, $x$ is in the maximal ideal of $A$ if and only if $x \in v$.

Lean: `New.IsPlaceOver` (Lib/ClassField/Places/GaloisDefs.lean).

A valuation subring lies over at most one prime of $K$. In the source this is `New.IsPlaceOver.unique` ([ValuationSubrings.lean](lean:Lib/ClassField/Places/ValuationSubrings.lean#L166)).

**Definition (Chosen place).** For a finite place $v$ of $K$ and an algebra structure of $\Omega = \bar{\mathbb{Q}}$ over $K$, the place $\bar v$ is a valuation subring of $\Omega$ over $v$, chosen by `Classical.epsilon`.

Lean: `New.placeOver` (Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean).

The proof that $\bar v$ lies over $v$ is `New.FinPlace.isPlaceOver_placeOver` ([ValuationSubrings.lean](lean:Lib/ClassField/Places/ValuationSubrings.lean#L193)). It finds one valuation subring over $v$, which dominates the local ring of $v$, and then applies the specification of `Classical.epsilon`. Without such a proof, $\bar v$ is an arbitrary valuation subring of $\Omega$.

**Theorem.** Let $\Gamma$ satisfy `IsProGalois Γ K Ω`, and let $A$ lie over $v$.

1. For a field $K \subset L \subset \Omega$ with $\Omega/L$ algebraic, $A$ lies over a prime $u$ of $L$ with $u$ over $v$.
2. If $A'$ also lies over $v$, then $g A = A'$ for some $g \in \Gamma$.

In the source, 1 is `New.IsPlaceOver.exists_above` ([ValuationSubrings.lean](lean:Lib/ClassField/Places/ValuationSubrings.lean#L328)) and 2 is `New.IsPlaceOver.exists_smul` ([ValuationSubrings.lean](lean:Lib/ClassField/Places/ValuationSubrings.lean#L342)).

The second statement is the transitivity of the Galois action on the primes over $v$ (Neukirch, Ch. I, Prop. 9.1), for the infinite extension $\Omega/K$. The source proves it with a compactness argument on $\Gamma$.

### Decomposition, inertia and Frobenius

**Definition (Decomposition group, Frobenius, inertia).** Let $\Gamma$ act on $\Omega$ and let $A$ be a valuation subring of $\Omega$. The decomposition group $D_A$ is the stabiliser of $A$ in $\Gamma$. For $q \in \mathbb{N}$, an element $\sigma \in \Gamma$ is a Frobenius for $q$ at $A$ if $\sigma \in D_A$ and $v_A(\sigma x - x^q) < 1$ for every $x$ with $v_A(x) \le 1$. The inertia group $I_A$ is the set of Frobenius elements for $q = 1$.

Lean: `New.decompGroup`, `New.IsFrob`, `New.inertiaGroup` (Lib/ClassField/Places/GaloisDefs.lean).

**Lemma.** If $\sigma$ and $\tau$ are Frobenius elements for the same $q$ at $A$, then $\sigma^{-1}\tau \in I_A$.

Lean: `New.IsFrob.inv_mul_mem_inertiaGroup` (Lib/ClassField/Places/GaloisDefs.lean).

**Remark (Formalization).** `New.IsFrob A q σ` is a property, not a function. The source does not define "the" Frobenius at a place. A statement that uses a Frobenius takes $\sigma$ and a proof of `IsFrob A q σ` as hypotheses, or obtains one from `New.IsPlaceOver.exists_isFrob`, which gives an element by an existence proof. So a value at a Frobenius is well defined only when it is constant on the coset $\sigma I_A$, for example for a representation unramified at $A$. The definition puts no condition on $q$. For $q$ not a power of the residue characteristic, the set of Frobenius elements can be empty. The useful case is $q = q_v$.

**Theorem.** Let $\Gamma$ satisfy `IsProGalois Γ K Ω`, with $\Omega$ algebraically closed of characteristic $0$ and $K$ a number field in $\Omega$, and let $A$ lie over $v$. Let $F$ be the fixed field of $D_A$. Then:

1. $F$ is a local field for $A$ in the sense of `New.IsLocalGalois`: $D_A$ is its Galois group, $A \cap F$ is a discrete valuation ring and its residue field is finite;
2. the residue field of $A \cap F$ has $q_v$ elements;
3. a uniformiser of $K$ for $A$ is a uniformiser of $F$ for $A$;
4. there is a Frobenius for $q_v$ at $A$.

Lean: `New.IsPlaceOver.isLocalGalois_and_residueCard_eq_and_isUniformiser`, `New.IsPlaceOver.exists_isFrob` (Lib/ClassField/Places/DecompositionCompletion.lean).

Classically, the decomposition field $F$ is the henselisation of $K$ at $v$ inside $\Omega$, it has the residue field of $v$ and the value group of $v$, and its completion is $K_v$ (Neukirch, Ch. II, §6 for henselian fields). The source proves 1 to 3 by an equivariant embedding of $\Omega$ into $\bar{\mathbb{Q}}_p$ that induces $A$. Then 4 follows from the Frobenius of the local field $F$, `New.IsLocalGalois.frobenius_spec`.

**Remark (Formalization).** The class `New.IsLocalGalois` does not ask that the field be complete or henselian. It asks that $\Gamma$ stabilise $A$, which over $F$ is equivalent to the uniqueness of the extension of the valuation to $\Omega$. The order function `New.ordRat` and the residue cardinal `New.residueCard` are chosen or have junk values: `New.ordRat K A` is an additive order on $\Omega^\times$ chosen with uniformisers of $K$ of order $1$, and `New.residueCard` is $0$ if the residue field is infinite. Statement 2 shows that the residue field of $F$ is finite.

**Theorem.** Let $A$ lie over $v$ in $K$ and over $w$ in a field $L$, $K \subset L \subset \Omega$, with $U \subset \Gamma$ open and the Galois group of $\Omega/L$. Let $e$ and $f$ be the ramification index and the inertia degree of $w$ over $v$. Then:

1. if $D_A \subset U$, then $q_w = q_v$ and the orders at $A$ normalised on $L$ and on $K$ agree;
2. if $I_A \subset U$, then $e = 1$;
3. the index of $U \cap D_A$ in $D_A$ is $e f$.

Lean: `New.IsPlaceOver.ramification_in_tower` (Lib/ClassField/Places/DecompositionCompletion.lean).

**Theorem.** Let $U \subset \Gamma$ be open. Then for all but finitely many finite places $v$ of $K$, $I_A \subset U$ for every $A$ over $v$.

In the source this is `New.finite_ramified` ([ValuationSubrings.lean](lean:Lib/ClassField/Places/ValuationSubrings.lean#L290)).

Classically these are the statements $|D| = ef$, $|I| = e$ for the finite extension $L/K$, with $L$ the fixed field of $U$, and the finiteness of the ramified primes (Neukirch, Ch. I, §9, and Ch. III, §2). The source proves `New.finite_ramified` by compactness of $\Gamma$: the inertia groups over $v$ tend to $1$ as $v$ leaves every finite set.

**Theorem.** Let $\Omega$ be algebraically closed of characteristic $0$, $N \ne 0$, $A$ a valuation subring with $v_A(N) = 1$, and $\sigma$ a Frobenius for $q$ at $A$. Then $\chi_N(\sigma) = q$ in $\mathbb{Z}/N$, and $\sigma$ fixes the $N$-th roots of unity if and only if $q \equiv 1 \bmod N$.

Lean: `New.IsFrob.cyclotomicCharMod_eq`, `New.IsFrob.mem_ker_cyclotomicCharMod_iff` (Lib/ClassField/Places/DecompositionCyclotomic.lean).

*Proof.* Let $\zeta$ be an $N$-th root of unity. Then $\sigma\zeta$ and $\zeta^q$ are $N$-th roots of unity, and $v_A(\sigma\zeta - \zeta^q) < 1$. Two distinct $N$-th roots of unity differ by a divisor of $N$ in $\mathbb{Z}[\zeta]$, which is a unit for $A$ since $v_A(N) = 1$. So $\sigma\zeta = \zeta^q$, and $\chi_N(\sigma) = q$ by the characterisation of Section 4. The second claim follows, since $\chi_N(\sigma) = 1$ if and only if $q \equiv 1 \bmod N$. $\square$

This is the classical fact that the Frobenius at $\mathfrak{p} \nmid N$ acts on $\mu_N$ by $\zeta \mapsto \zeta^{N\mathfrak{p}}$ (Neukirch, Ch. I, Prop. 10.3, for $K = \mathbb{Q}$). With $q = q_v$, it gives the splitting of $v$ in $K(\zeta_N)$ that [the field E](/chapter/fields-places-twists/) uses for $E$ and the place classes.
