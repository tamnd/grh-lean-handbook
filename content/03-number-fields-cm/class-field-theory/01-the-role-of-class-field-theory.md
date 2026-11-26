---
title: The role of class field theory
lean:
  - Lib/ClassField/Global/Chebotarev.lean
  - Lib/ClassField/Global/ExistenceTheorem.lean
  - Lib/ClassField/HeckeL/ContinuationAtOne.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The role of class field theory

The source uses class field theory as a tool. It does not need the full classification of abelian extensions of a number field. It needs three consequences, and it proves each of them in the folder `Lib/ClassField`. This chapter explains these proofs. It states each result in the form that Lean states it, and it compares that form with the textbook form.

The three consequences are these.

1. **Chebotarev as an existence statement.** Let $K$ be a number field and let $W$ be a nonempty open subset of $\operatorname{Gal}(\bar{\mathbb{Q}}/K)$. Then there are infinitely many finite places $v$ of $K$ of prime norm whose Frobenius elements lie in $W$. The source states this as [Theorem](/decl/New.chebotarev/). It gives no density.
2. **Existence for totally complex fields.** Let $K$ be totally complex. A continuous homomorphism from the finite ideles of $K$ that is trivial on $K^\times$ comes from a continuous homomorphism of the Galois group, through the Artin map. The source states this as [Theorem](/decl/New.exists_comp_artinMap/).
3. **Nonvanishing of Hecke $L$-functions at $s = 1$.** Let $\psi$ be the finite part of a Hecke character with $\psi^2 \neq 1$. Then the partial Euler product of $\psi$ has no zero at real $s \geq 1$. The source states this as [Theorem](/decl/New.IsHeckeOfType.eulerProd_ne_zero/).

### Where the results are used

The main argument of the source is outlined in [the plan](/chapter/theorem-and-plan/). Class field theory enters it at several points. The Chebotarev statement is applied in `Lib/GaloisRep/Main/Defs.lean` and `Lib/GaloisRep/Main/OddRank.lean`, where the source finds primes whose Frobenius elements have a given image under a Galois representation. It is also applied in `Lib/ClassField/Grunwald.lean` and in two files of `Lib/ClassField/GreenbergWiles`. The chapter [local duality and the Greenberg-Wiles count](/chapter/local-duality/) explains those files. The existence theorem is applied in `Lib/ClassField/Grunwald.lean`, in `Lib/PadicHodge/Characters.lean` and in `New/Congruences/Selmer/AuxiliaryPrimes.lean`. In each case it makes a Galois character from a character of the ideles. The nonvanishing at $s = 1$ is applied in `Lib/ClassField/Avatar/HeckeBaseChange.lean`. Several files of `New/` also use the Euler products of `Lib/ClassField/HeckeL`, for example `New/Spanning/MainTerm/Frequencies.lean`.

### The form of the theory

The textbook theory has two forms. The first form uses ideals and ray class groups. The second form uses ideles and the idele class group. Section 2 recalls both. The source uses a third form. It uses only the *finite* ideles $(\mathbb{A}_{K,f})^\times$, and it puts the condition at the real places into a subgroup: the principal ideles of the *totally positive* elements of $K^\times$. For a totally complex field this is no restriction, since every element is totally positive in the empty sense. This is one reason why the existence theorem is stated only for totally complex fields.

The source also uses its own form of Galois cohomology. It does not use the group cohomology of Mathlib for profinite groups. It defines continuous cochains with values in a discrete module, by explicit formulas, in degrees 1 and 2 only. The Brauer group of a local field is the group $H^2(\Gamma, \Omega^\times)$ of these explicit cochains, where $\Omega$ is an algebraic closure. Section 4 explains this.

### A sketch of the proof

The source follows the classical order of the cohomological proof, with an analytic second inequality. It does not follow one textbook. The steps are these.

1. **Local theory** (Section 4). For a henselian discretely valued field $k$ of characteristic 0 with finite residue field, the source proves that the explicit $H^2(\Gamma_k, \Omega^\times)$ is isomorphic to $\mathbb{Q}/\mathbb{Z}$. The tool for the norm index in prime degree is Tate's index formula. From the invariant map and Pontryagin duality the source gets a local Artin map.
2. **The global Artin map** (Section 5). The global map is a product of local maps. The source chooses it by `Classical.epsilon` and then proves that the choice has the product formula.
3. **Hecke $L$-functions** (Section 5). The source proves that a partial Hecke $L$-function of a Hecke character $\psi \neq 1$ extends past $s = 1$ along the real line. It uses a theta sum in place of Poisson summation. From this it gets the prime densities that the second inequality needs.
4. **The second inequality** (Section 5). For a Galois extension $L/K$, an open subgroup of the finite ideles that contains the totally positive elements and the norms from $L$ has index at most $[L : K]$.
5. **Albert, Brauer, Hasse and Noether** (Section 6). A class in the global Brauer group that is locally zero is zero. The source proves a form with a hypothesis at the real places that is stronger than the textbook hypothesis.
6. **Reciprocity** (Section 7). The Artin map kills the totally positive elements of $K^\times$. The source follows Artin's method with cyclotomic characters.
7. **Norm theorems** (Section 7). The Artin map is surjective, its kernel on the extension cut out by a character is the norm group, and the Hasse norm theorem holds for cyclic extensions.
8. **Existence and Chebotarev** (Section 8). For totally complex $K$, the existence theorem comes from Kummer theory and the norm theorems. Chebotarev comes from the second inequality and the surjectivity of the Artin map.

Section 3 fixes the setting: the field $\Omega$, the places of $\Omega$, Frobenius elements and finite ideles. The chapter [CM fields and places](/chapter/cm-fields/) explains the fields and the places in more detail. Section 9 gives a table of the differences between the source and Milne's notes *Class Field Theory*, the exercises, and the references.

### What the chapter does not claim

The source claims that Lean accepts these proofs, if the reported checks hold. This chapter explains what the statements say and how the proofs go. It does not say that the proofs are correct. Where a statement in the source is weaker than the textbook statement, the chapter says so. Where a definition is a choice by `Classical.epsilon`, the chapter says which lemma proves that the choice has its property.
