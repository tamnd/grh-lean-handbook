---
title: The model and the chain to the main theorem
lean:
  - Lib/Shimura/IntegralModel/TowerExistence.lean
  - Lib/Shimura/HeckeTower/Model.lean
  - Lib/GaloisRep/Main/SeedRepresentation.lean
  - Lib/Shimura/Eigenspace.lean
decls:
  - New.Variety.exists_model
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The model and the chain to the main theorem

A Galois representation attached to an automorphic form is usually found in the étale cohomology of a Shimura variety. To control it at a prime $p$, one needs the variety over a ring in which $p$ is not inverted. This is an *integral model*. Its special fibre carries the Frobenius, and the congruence relation of Eichler, Shimura and Kottwitz compares the Frobenius with a Hecke correspondence. This chapter explains how the source builds its integral model without a moduli problem, and proves the main steps.

### The textbook model

The textbook model is a moduli space. Let $(B, {}^*, V, \langle\,,\rangle, h)$ be a PEL datum in the sense of Kottwitz, *Points on some Shimura varieties over finite fields*, J. Amer. Math. Soc. 5 (1992), §5. Let $p$ be a prime at which the datum is unramified, and let $K^p$ be a small enough compact open subgroup of the group of the datum at the finite places prime to $p$. Kottwitz defines a functor on schemes over $\mathcal{O}_{E} \otimes \mathbb{Z}_{(p)}$, with $E$ the reflex field. It sends $S$ to the isomorphism classes of tuples $(A, \lambda, i, \bar\eta)$: an abelian scheme $A$ over $S$ up to prime to $p$ isogeny, a polarization $\lambda$ of degree prime to $p$, an action $i$ of an order of $B$ that satisfies the determinant condition, and a class $\bar\eta$ of level structures prime to $p$ modulo $K^p$. Kottwitz shows in §5 that a smooth quasi-projective scheme represents it. Harris and Taylor, *The geometry and cohomology of some simple Shimura varieties* (2001), Chapter III, give the construction for the unitary groups of signature $(1, n-1)$ that occur here.

The moduli problem gives the scheme, its smoothness from deformation theory, the Hecke correspondences, and the points over finite fields. The congruence relation comes from the points over $\bar{\mathbb{F}}_p$.

### The model of the source

The source does not formalize the moduli functor. It formalizes no representability theorem. In its place it defines a structure `New.Variety.Model` that lists the properties of a tower of integral Kuga-Sato varieties that the later chapters use. Then it proves that a structure of this type exists. Section 7 states the structure in full. In short: a smooth proper base $Z$ over $R$, reduced projective covers $W_i$ with legs $p_g : W_i \to Z$, a finite group $\Delta_i$ for which $p_1$ is a Galois covering, complex points given by moduli points, a tangent formula, and a congruence relation at every safe split place.

In the theorem, $E$ is a CM field with a base place, $d_0 \equiv 3 \pmod 4$ with $\mathbb{Q}(\sqrt{-d_0}) \subseteq E$, and $D$ is a PEL datum of the source (Section 2). Universal families are defined in Section 6, neat levels in Section 7, and safe places in Section 2.

**Theorem (Existence of the model).** Let $E$ be a field with a base place, let $d_0$ satisfy `HasQuadSubfield` for $E$, let $R$ be an $\mathcal{O}_E$-subalgebra of $E$, and let $D$ be a PEL datum of the source for $E$. Let $U$ be a universal family for $D$ over $R$. Assume that the level $\mathfrak{N} = D.\mathrm{level}$ is neat, that $D.\beta$ is the image of $(1 + \sqrt{-d_0})/2$, and that $D$ is good at every finite place $w$ that is safe for $\mathfrak{N}$. Then for every $\nu \neq 0$ there is a model `Model D.Index d₀ 𝔑 ν R`.

Lean: `New.Variety.exists_model` (Lib/Shimura/IntegralModel/TowerExistence.lean).

The proof is in Section 7.

**Remark (Formalization).** The conclusion is `Nonempty (Model D.Index d₀ D.level ν R)`. Only the fields of the structure are available to a user. The base $Z$ is not shown to represent a functor, and no two models are compared. This is enough for [Chapter 3](/chapter/congruence-relation/) and [Chapter 4](/chapter/attached-representations/), which use the cohomology of the covers $W_i$ and the fields `covering`, `tangent` and `congruence`.

### The chain to the main theorem

The theorem is used once, in `Lib/GaloisRep/Main/SeedRepresentation.lean`.

1. `New.GaloisRep.sphericalCompat_std` (Lib/GaloisRep/Main/AllRanks.lean, line 465) builds compatible systems of Galois representations of every rank with the next lemma.
2. `New.GaloisRep.exists_rep_of_cuspidal_type` (SeedRepresentation.lean, line 822) builds one representation for a cuspidal datum. At line 716 it applies `New.Variety.exists_pel` (Section 2), and it makes the level neat with `New.Variety.eventually_isNeat` (Section 7).
3. The private lemma `exists_padicRep_of_pel` (SeedRepresentation.lean, line 514) takes the PEL datum. It localizes $\mathcal{O}_E$ at the intersection $M$ of the complements of the safe places, so the maximal ideals of $R$ are the safe places. At line 543 it applies `New.Variety.ThetaNull.nonempty_universalFamily` (Section 6) and then the theorem above with $\nu + 1$.
4. At line 544 it applies `New.Variety.Model.exists_galois_rep` (Lib/Shimura/Eigenspace.lean, line 689) to the model. That theorem is the subject of [Chapter 3](/chapter/congruence-relation/).

So three results of this chapter enter the main proof: the existence of PEL data, of the universal family, and of the model.

**Remark (Formalization).** The source uses no compactification. The field `proper` of the model says that $Z$ is proper over $\operatorname{Spec} R$. In the source this holds by construction, since the base is closed in a projective space over $R$. In the textbook, properness comes from the anisotropy of the group, and Harris and Taylor choose their data so that this holds.

### The model case

Take $n = 1$. Then the PEL datum has rank $1$, the moduli points have one coordinate, and the ball of dimension $n - 1 = 0$ is a point. The universal family of Section 6 has a base that is smooth of relative dimension $0$ over $R$, so it is étale over $\operatorname{Spec} R$. Its fibres are abelian varieties of dimension $[E : \mathbb{Q}]/2$ with complex multiplication by $\mathcal{O}_E$, and its complex points are finitely many CM points. The congruence relation is then a statement on the Frobenius of a CM abelian variety.

### The plan of the chapter

The textbook proof goes from the moduli problem to the scheme. The source goes from complex points to the scheme. It takes the complex tori of the uniformization of [Chapter 1](/chapter/complex-abelian-varieties/), takes the values of their theta functions at torsion points (the *theta-null values*), and takes the closure of these values in a projective space over $R$. Then it proves that the closure has the properties that the moduli space would have. The sections follow the steps of this construction.

1. Section 2: the PEL datum of the source and its existence.
2. Section 3: theta tori, and good reduction of their theta functions at a good place.
3. Section 4: Riemann's theta relation, and the normal generation of the theta functions modulo a good place.
4. Section 5: the flat closure of the theta-null points and the theta family over it.
5. Section 6: the universal family, and the bound $n - 1$ on the tangent space that gives smoothness.
6. Section 7: the structure `Model`, neat levels, extension over arcs, and the proof of the theorem above.
7. Section 8: exercises and notes.

Section 4 and Section 5 replace the moduli problem. In the source, the fibres over a finite field are fibres of a closure, and one must prove that they are abelian varieties. The tool for this is Mumford's theory of theta-null values and Riemann's relation, as in Mumford, *On the equations defining abelian varieties I*, Invent. Math. 1 (1966), 287 to 354.
