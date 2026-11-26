---
title: What the chapter proves
lean:
  - New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter attaches to each eigensystem of the lifts one $\ell$-adic representation $T$ of the absolute Galois group of the CM field $E$ of the data. The representation $T$ has the rank $r$ of the smaller hermitian space, and it gives the traces of the representations attached to *all* twisted lifts of the system. Such a $T$ is a *main summand*. The chapter also defines the objects with which the later chapters of this volume measure the cost of a congruence: the modules of cocycles that obey the relations of a family, the crystalline Selmer length, the crystalline colength and the defect bound at $\ell$. This is Step 2 of [the chain of the proof](/chapter/regular-families-plan/#the-chain-of-the-proof). The plan of the whole argument is in [the theorem and the plan](/chapter/theorem-and-plan/).

### The main theorem

Fix the data $D$ of [the data and its sizes](/chapter/data-and-sizes/), with the spaces $W_m$ of rank $r$ and $V$ of rank $n = r + t$. A good form on $W_m$ is a form of the good part of the space, and an eigensystem $p$ is a function that gives a Hecke value $p(w, i)$ at each split place $w$ and each index $i$.

**Theorem (Main summands of the lifts, short form).** Let $p$ be an eigensystem that occurs in a nonzero good form on $W_m$, and let $j$ be a lift index of $D$. Then there is a representation $T$ of rank $r$ that is a main summand for the $j$-th descent pair of the trivial twist and the Hecke values $p$.

Lean: `New.Selmer.exists_isMainSummand_descentPair` (New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean).

The section [main summands from eigensystems](/chapter/main-summands/#main-summands-from-eigensystems) states the theorem in full and proves it. The condition "main summand" has two parts. The first part says that $T$ is like a main summand: $T$ is conjugate self-dual, its jumps obey explicit inequalities in terms of the sizes of $D$, its inertia above the level primes $p_0, p_1$ is tame and controlled, its image spans the matrices, and its image contains suitable scalars. The second part says that for every twist $\vartheta$ and every lift $y$ of the system to a descent pair with the twisted character, the normalized representation attached to $y$ has the trace of $\vartheta^{-1} T$ plus $1, \varepsilon^{-1}, \dots, \varepsilon^{-(t'-1)}$, where $\varepsilon$ is the cyclotomic character and $t'$ is the difference of ranks of the pair.

### The sketch of the proof

The proof has four steps.

1. *A label.* A nonzero good eigenform $z$ is a sum of the projections $e_c z$ over the tuples $c$ of labels of the good tuple families. So some $e_c z \neq 0$. The tuple $c$ fixes the type of the inertia at the chosen places above $p_0$ and $p_1$. With this $c$ the descent pair is a *lift setting*.
2. *A representation of a type.* The building theorems of Volume 8 give a representation $R$ attached to the eigenform. The local conditions at the chosen places, the conjugate places and the other places make $R$ a *representation of the type* of the lift setting.
3. *Main summand like.* A representation of the type with weights that satisfy the inequalities is like a main summand. The scalars come from a tame inertia element at a chosen place. Its eigenvalues are the roots of a primitive label or of $X - 1$, and a common root power of them is a scalar.
4. *The traces.* A twist of $R$ by an algebraic character is the representation $T$. The trace identity holds at most Frobenius elements by the Hecke polynomials of the lifts. It passes to all of $G$ by density and continuity.

The weights are the heart of the matter. The jumps of $T$ at a complex embedding $\sigma$ are $t/2 - \epsilon_\sigma(\lambda_q + w_j)$ for $q < r$, where $\lambda_q$ are the target parameters, $w_j$ is the $j$-th lift weight and $\epsilon_\sigma = \pm 1$ is the sign of $\sigma$. The section [weights, signs and b-places](/chapter/main-summands/#weights-signs-and-b-places) shows that these numbers are either large, or close to $-\epsilon_\sigma w_j$. That shape is what the local loss at $\ell$ needs.

### The results that earlier chapters cite

Three merged chapters of this volume use results of this chapter. They are stated and proved here.

- [Ribet's element for Galois representations](/chapter/ribet-elements/#ribets-element-for-galois-representations) uses lift settings, representations of a type, the crystalline Selmer length, the crystalline colength, main summands, the twist error and the defect bound. They are in the sections [cocycles, relations and Selmer lengths](/chapter/main-summands/#cocycles-relations-and-selmer-lengths) and [lift settings and representations of a type](/chapter/main-summands/#lift-settings-and-representations-of-a-type).
- [The matrices for the block and the characters](/chapter/ribet-elements/#the-matrices-for-the-block-and-the-characters) uses the modules $\mathrm{Coc}(\rho, B)$ of cocycles that obey the relations of a family. They are defined in [cocycles, relations and Selmer lengths](/chapter/main-summands/#cocycles-relations-and-selmer-lengths).
- [Root chains of weak lifts](/chapter/first-order-deformations/#root-chains-of-weak-lifts) uses the normalizing character $\chi$ and the normalized representation $u = \chi \otimes \rho$. They are defined in [avatars and conjugate self-duality](/chapter/main-summands/#avatars-and-conjugate-self-duality).
- [The plan of the volume](/chapter/regular-families-plan/#the-chain-of-the-proof) states the theorem on main summands of the lifts.

One citation in [Ribet's element for Galois representations](/chapter/ribet-elements/#ribets-element-for-galois-representations) points here for the auxiliary twist $\psi$. That object is defined in [tied traces and even classes](/chapter/tied-traces/). This chapter recalls it in one line in the section on lift settings.

### What the chapter uses

The chapter uses the following background. Each item is recalled in one line where it is used.

- CM fields, complex conjugation and the sign of an embedding ([CM fields](/chapter/cm-fields/)); the class field theory of the avatar of an algebraic Hecke character ([class field theory](/chapter/class-field-theory/)).
- Labels, tuple idempotents and primitive polynomials of the finite general linear group ([the finite general linear group](/chapter/finite-gln/)).
- Crystalline cocycles and lengths over a discrete valuation ring ([period rings](/chapter/period-rings/), [Fitting ideals](/chapter/fitting-ideals/)).
- The meaning of "attached" and the local conditions ([what attached means](/chapter/attached-representations/)), and the existence of attached representations with local-global compatibility at split places ([building the representations](/chapter/building-representations/)).
- Descent pairs, Hecke polynomials of lifts and critical pairs ([single theta lifts](/chapter/single-theta-lifts/), [twists and critical pairs](/chapter/twists-critical-pairs/)).
- The tied traces and the auxiliary primes of [tied traces and even classes](/chapter/tied-traces/), the chapter before this one.

No file of this chapter imports a file that `volume.yaml` places in a later chapter of Volume 12. The forward links of this chapter only say where a result is used.

### The plan of the chapter

The sections follow the order of need. Section 2 treats the weights, the signs of embeddings and the b-places. Section 3 defines the cocycle modules and the Selmer lengths. Section 4 treats avatars and conjugate self-duality. Section 5 defines lift settings and representations of a type. Section 6 proves that a representation of the type is like a main summand. Section 7 treats the auxiliary places and the base level. Section 8 proves the main theorem. Section 9 has exercises and notes.
