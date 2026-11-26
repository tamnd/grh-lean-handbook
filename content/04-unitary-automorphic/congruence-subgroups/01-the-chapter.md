---
title: Congruence subgroups and Haar moduli
lean:
  - Lib/General/Groups/CongruenceSubgroups.lean
  - Lib/General/Groups/IndexOfProduct.lean
  - Lib/General/Groups/ProfiniteCharacters.lean
  - Lib/General/Groups/BesselGroups.lean
  - Lib/General/Groups/CharacterTheory.lean
  - Lib/General/Measure/HaarModulus.lean
  - Lib/General/Measure/HaarNormalisation.lean
  - Lib/General/Measure/FibreMeasure.lean
  - Lib/General/Measure/IdempotentKernel.lean
  - Lib/General/Measure/IntegralOperators.lean
  - Lib/General/Measure/QuadricDisintegration.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Congruence subgroups and Haar moduli

This chapter collects the tools of group theory and of measure theory that the rest of the source uses on unitary groups, on general linear groups over local rings, and on profinite Galois groups. The tools are standard. They are congruence subgroups of $\mathrm{GL}_n$, unitary groups as topological groups, characters of profinite groups with values in $\mathbb{Q}/\mathbb{Z}$, the modulus of a linear map on a locally compact ring, integrals over compact open subgroups, and the character theory of finite groups. None of them is a step of the main argument. Each of them is an input to a step. The chapter states each tool in its textbook form, then in the form of the source, and it says where the two differ.

### Where the chapter sits

The plan of the proof is in [the theorem and the plan](/chapter/theorem-and-plan/). The proof has three main theorems, A, B and C, and each of them works with automorphic forms on unitary groups. The forms live on adelic quotients. The local factors of these quotients are groups such as $\mathrm{U}(J)(\mathbb{Q}_p)$ and $\mathrm{GL}_n(\mathbb{Z}_p)$. The proofs integrate over such groups, count cosets of compact open subgroups, and change variables by linear maps. This chapter supplies the facts that make these operations exact.

The users of the chapter are many. Congruence subgroups appear in the objects of Theorem A ([the objects of the upper bound](/chapter/upper-bound-objects/)). The modulus of a linear map and its integer form, the generalised index, appear in the main term of Theorem B ([the main term](/chapter/main-term/) and [the finite densities](/chapter/finite-densities/)). The duality of profinite characters gives the Artin maps of [class field theory](/chapter/class-field-theory/). The character theory of finite groups is the base of [the characters of finite general linear groups](/chapter/finite-gln/). The idempotent kernels and the fibre measures are used at the real place of Theorem B ([the Bessel functions at the real place](/chapter/bessel-real-place/)).

The chapter uses the adeles and the hermitian spaces of [the first chapter of this volume](/chapter/adeles-hermitian-spaces/). That chapter defines the unitary group $\mathrm{U}(J)$ of a matrix $J$, the sign matrices, and the group $\mathrm{GL}_n(O)$ of a subring $O$. This chapter does not define them again. It links to [the definition](/decl/New.U/).

### The model case

The whole chapter generalises one example. Let $p$ be a prime, let $G = \mathrm{GL}_2(\mathbb{Q}_p)$ and let $K = \mathrm{GL}_2(\mathbb{Z}_p)$. The group $K$ is compact and open in $G$. For $k \geq 1$, the *principal congruence subgroup of level $p^k$* is
$$\Gamma(p^k) = \{ g \in K : g \equiv 1 \pmod{p^k} \},$$
the kernel of the reduction map $K \to \mathrm{GL}_2(\mathbb{Z}/p^k\mathbb{Z})$. The reduction map is onto, because a matrix over $\mathbb{Z}_p$ whose determinant is a unit modulo $p$ is invertible over $\mathbb{Z}_p$. So
$$[K : \Gamma(p^k)] = |\mathrm{GL}_2(\mathbb{Z}/p^k\mathbb{Z})| = p^{4(k-1)}(p^2 - 1)(p^2 - p).$$
The groups $\Gamma(p^k)$ form a basis of neighbourhoods of $1$ in $G$. So $K$ is a profinite group, the inverse limit of the finite groups $\mathrm{GL}_2(\mathbb{Z}/p^k\mathbb{Z})$.

Haar measure enters through the modulus. Let $\mu$ be a Haar measure on $\mathbb{Q}_p^2$, and let $g \in G$. Then $E \mapsto \mu(gE)$ is again a Haar measure, so $\mu(gE) = \Delta(g)\mu(E)$ for a constant $\Delta(g) > 0$. Take $E = \mathbb{Z}_p^2$. If $g = \mathrm{diag}(p, 1)$, then $g\mathbb{Z}_p^2 = p\mathbb{Z}_p \oplus \mathbb{Z}_p$ has index $p$ in $\mathbb{Z}_p^2$, so $\Delta(g) = p^{-1}$. If $g \in K$, then $g\mathbb{Z}_p^2 = \mathbb{Z}_p^2$, so $\Delta(g) = 1$. Each $g \in G$ is a product $k_1 \, \mathrm{diag}(p^a, p^b) \, k_2$ with $k_1, k_2 \in K$, by the theory of elementary divisors. So
$$\Delta(g) = p^{-(a+b)} = |\det g|_p.$$
The inverse $\Delta(g)^{-1} = p^{a+b}$ is an integer when $g$ has entries in $\mathbb{Z}_p$: it is the index $[\mathbb{Z}_p^2 : g\mathbb{Z}_p^2]$. This integer form of the modulus is the *generalised index* of the source.

Characters enter through duality. A continuous homomorphism $\chi : \mathbb{Z}_p \to \mathbb{Q}/\mathbb{Z}$ has an open kernel, because $\mathbb{Q}/\mathbb{Z}$ is discrete. So $\chi$ kills $p^k\mathbb{Z}_p$ for some $k$, and $\chi$ is a character of the finite group $\mathbb{Z}/p^k\mathbb{Z}$. The characters of $\mathbb{Z}/p^k\mathbb{Z}$ are the maps $x \mapsto ax/p^k$ with $a \in \mathbb{Z}/p^k\mathbb{Z}$. So the group of characters of $\mathbb{Z}_p$ is $\mathbb{Q}_p/\mathbb{Z}_p$, and each additive map from this group to $\mathbb{Q}/\mathbb{Z}$ is evaluation at a point of $\mathbb{Z}_p$. This is Pontryagin duality for a profinite abelian group. Section 4 proves the general form that the source uses.

### The sections

Section 2 treats integral matrices and congruence subgroups of $\mathrm{GL}_n$, with the block triangular, Levi and parahoric subgroups. Section 3 treats unitary groups as topological groups: they are closed, and the definite ones are compact. Section 4 treats characters of profinite groups and the extension of homomorphisms into divisible groups. Section 5 computes the modulus of an invertible matrix over a locally compact ring, and its integer form. Section 6 collects the integration tools: uniqueness of Haar measure, orthogonality on subgroups, Gaussian normalisation, a layer cake bound, idempotent kernels, fibre measures, and the disintegration of a quadric. Section 7 treats the character theory of finite groups in the form of the source. Section 8 has the exercises and the notes.

The chapter has one theme that runs through all the sections. A textbook statement often needs a quantity that can be infinite or undefined: an index, a measure, an inverse. The source works with total functions. So an infinite index is read as $0$, an infinite measure has real part $0$, and the ring inverse of a non-unit is $0$. Each statement of the chapter says where such a value can appear, and why the argument does not see it.

Lean accepts the statements of this chapter if the checks that the source reports hold. This book did not rerun the checks ([the claim and its status](/chapter/claim-and-status/)).
