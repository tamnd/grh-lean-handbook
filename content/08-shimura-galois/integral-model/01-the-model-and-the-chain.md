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

A Galois representation attached to an automorphic form is usually found in the étale cohomology of a Shimura variety. To control it at a prime $p$, one needs the variety over a ring in which $p$ is not inverted. This is an *integral model*. Its special fibre carries the Frobenius, and the congruence relation of Eichler, Shimura and Kottwitz compares the Frobenius with a Hecke correspondence. This chapter explains how the source builds the integral model that it uses. The source builds it without a moduli problem. The chapter states what the source proves about the model and gives the proofs at the level of the main steps.

### The textbook model

The textbook model is a moduli space. Let $(B, {}^*, V, \langle\,,\rangle, h)$ be a PEL datum in the sense of Kottwitz, *Points on some Shimura varieties over finite fields*, J. Amer. Math. Soc. 5 (1992), §5. Let $p$ be a prime at which the datum is unramified, and let $K^p$ be a small enough compact open subgroup of the group of the datum at the finite places prime to $p$. Kottwitz defines a functor on schemes over $\mathcal{O}_{E} \otimes \mathbb{Z}_{(p)}$, with $E$ the reflex field. It sends $S$ to the isomorphism classes of tuples $(A, \lambda, i, \bar\eta)$: an abelian scheme $A$ over $S$ up to prime to $p$ isogeny, a polarization $\lambda$ of degree prime to $p$, an action $i$ of an order of $B$ that satisfies the determinant condition, and a class $\bar\eta$ of level structures prime to $p$ modulo $K^p$. Kottwitz shows in §5 that the functor is represented by a smooth quasi-projective scheme. The proof uses the moduli of polarized abelian schemes with level structure (Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, Chapter 7) and the deformation theory of abelian schemes. The book of Harris and Taylor, *The geometry and cohomology of some simple Shimura varieties* (2001), Chapter III, gives the same construction for the unitary groups of signature $(1, n-1)$ that occur here. A modern account of the general case is in Lan, *Arithmetic compactifications of PEL-type Shimura varieties* (2013), Chapter 1. For the complex points and the groups, see Milne, *Introduction to Shimura varieties*, §8.

The moduli problem gives many things at once: the scheme, its smoothness from deformation theory, the Hecke correspondences from the action on level structures, and the points over finite fields as isogeny classes of abelian varieties with extra structure. The congruence relation then comes from the description of the points over $\bar{\mathbb{F}}_p$.

### The model of the source

The source does not formalize the moduli functor. It formalizes no representability theorem. In its place it defines a structure `New.Variety.Model` that lists the properties of a tower of integral Kuga-Sato varieties that the later chapters use. Then it proves that a structure of this type exists. Section 7 states the structure in full. Here is its content in short. Over the ring $R$ there is a base scheme $Z$, smooth and proper of some relative dimension. For each level $i$ there is a reduced projective scheme $W_i$ with finitely many maps $p_g : W_i \to Z$, called legs. A finite group $\Delta_i$ acts on $W_i$, and the leg $p_1$ is a Galois covering with group $\Delta_i$ on complex points. The complex points of $W_i$ are the classes of analytic moduli points. A tangent formula holds at the fixed points of the legs, and a congruence relation holds at every safe split place.

The existence theorem is the main result of this chapter. The notions in it are the following. $E$ is a CM field with a base place (Section 2). $d_0 \equiv 3 \pmod 4$, and $E$ is an algebra over $\mathbb{Q}(\sqrt{-d_0})$. $R$ is a subalgebra of $E$ over $\mathcal{O}_E$. $D$ is a PEL datum of the source (Section 2). A universal family over $R$ is the output of Section 6. A level is neat if it kills the automorphisms of moduli points (Section 7). A place is safe for the level if it is split over $\mathbb{Q}(\sqrt{-d_0})$ in a strong sense and prime to the level (Section 2).

**Theorem (Existence of the model).** Let $E$ be a field with a base place, let $d_0$ satisfy `HasQuadSubfield` for $E$, let $R$ be an $\mathcal{O}_E$-subalgebra of $E$, and let $D$ be a PEL datum of the source for $E$. Let $U$ be a universal family for $D$ over $R$. Assume that the level $\mathfrak{N} = D.\mathrm{level}$ is neat, that $D.\beta$ is the image of $(1 + \sqrt{-d_0})/2$, and that $D$ is good at every finite place $w$ that is safe for $\mathfrak{N}$. Then for every $\nu \neq 0$ there is a model `Model D.Index d₀ 𝔑 ν R`.

Lean: `New.Variety.exists_model` (Lib/Shimura/IntegralModel/TowerExistence.lean).

The theorem is an existence statement. It gives a term of the type `Model`, and the later chapters use only the fields of that term. The proof is in Section 7.

**Remark (Formalization).** The conclusion is `Nonempty (Model D.Index d₀ D.level ν R)`. No property of the model outside the fields of the structure is available to a user of the theorem. In particular the base $Z$ is not shown to represent a functor, and no two models are compared. The docstring of `New.Variety.Model` in `Lib/Shimura/HeckeTower/Model.lean` says that the model is "given by a list of properties". For the argument this is enough: the Galois representation of [Chapter 3](/chapter/congruence-relation/) and of [Chapter 4](/chapter/attached-representations/) is built from the cohomology of the covers $W_i$, and its local properties come from the fields `covering`, `tangent` and `congruence`.

### The chain to the main theorem

The theorem above is used once, in a private lemma of `Lib/GaloisRep/Main/SeedRepresentation.lean`. The chain from the top is the following.

1. `New.GaloisRep.sphericalCompat_std` (Lib/GaloisRep/Main/AllRanks.lean, line 465) builds compatible systems of Galois representations of every rank. It applies the next lemma.
2. `New.GaloisRep.exists_rep_of_cuspidal_type` (SeedRepresentation.lean, line 822) builds one representation for a cuspidal datum. At line 716 its proof applies `New.Variety.exists_pel` (Section 2) to get a CM type $\Psi$, a natural number $N$, and PEL data at every level divisible by $N$. It then takes an auxiliary split place $w_1$ with `New.Variety.eventually_isNeat` (Section 7) so that the level is neat.
3. The private lemma `exists_padicRep_of_pel` (SeedRepresentation.lean, line 514) takes the PEL datum. It sets $M$ to be the intersection of the complements of the safe places, and $R$ to be the localization of $\mathcal{O}_E$ at $M$, as a subalgebra of $E$. Thus the maximal ideals of $R$ are exactly the safe places. At line 543 it applies `New.Variety.ThetaNull.nonempty_universalFamily` (Section 6) and then the theorem above with $\nu + 1$.
4. At line 544 it applies `New.Variety.Model.exists_galois_rep` (Lib/Shimura/Eigenspace.lean, line 689) to the model. That theorem is the subject of [Chapter 3](/chapter/congruence-relation/).

So three results of this chapter enter the main proof: the existence of PEL data, the existence of the universal family, and the existence of the model. The rest of the chapter proves them.

**Remark (Formalization).** The source uses no compactification. The field `proper` of the model says that $Z$ is proper over $\operatorname{Spec} R$. In the source this holds by construction: the base is a closed subscheme of a projective space over $R$ (Section 5 and Section 7). In the textbook, properness of the moduli space comes from the anisotropy of the group, and Harris and Taylor choose their data so that this holds. The source asks $E$ to have at least two infinite places (the class `New.CMBase`), and the signature condition of Section 3 makes the action at the places $v \neq v_0$ different from the action at $v_0$.

### The model case

Take $n = 1$. Then the PEL datum has rank $1$, the moduli points have one coordinate, and the ball of dimension $n - 1 = 0$ is a point. The universal family of Section 6 has a base that is smooth of relative dimension $0$ over $R$, so it is étale over $\operatorname{Spec} R$. Its fibres are abelian varieties of dimension `abelianDim` $= 1 \cdot [E : \mathbb{Q}]/2$ with complex multiplication by $\mathcal{O}_E$. The complex points are finitely many CM points. In this case the congruence relation is a statement on the Frobenius of a CM abelian variety, of the same kind as the formula of Shimura and Taniyama. The reader can keep this case in mind: every construction of the chapter makes sense for it, and the only part that becomes empty is the deformation theory of Section 6.

### The plan of the chapter

The textbook proof goes from the moduli problem to the scheme. The source goes from complex points to the scheme. It takes the complex tori of the uniformization of [Chapter 1](/chapter/complex-abelian-varieties/), takes the values of their theta functions at torsion points (the *theta-null values*), and takes the closure of these values in a projective space over $R$. Then it proves that the closure has the properties that the moduli space would have. The sections follow the steps of this construction.

1. Section 2: the PEL datum of the source and its existence.
2. Section 3: theta tori, and good reduction of their theta functions at a good place.
3. Section 4: Riemann's theta relation, and the normal generation of the theta functions modulo a good place.
4. Section 5: the flat closure of the theta-null points, the theta family over it, and extension of morphisms over arcs.
5. Section 6: the universal family, and the bound $n - 1$ on the tangent space that gives smoothness.
6. Section 7: the Hecke tower, the structure `Model`, neat levels, and the proof of the theorem above.
7. Section 8: exercises and notes.

Section 4 and Section 5 replace the moduli problem. In the textbook, the fibres of the moduli space over a finite field are abelian varieties by definition. In the source, they are fibres of a closure, and one must prove that they are abelian varieties. The tool for this is Mumford's theory of theta-null values and Riemann's relation, as in Mumford, *On the equations defining abelian varieties I*, Invent. Math. 1 (1966), 287 to 354.
