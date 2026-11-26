---
title: CM fields in the argument
lean:
  - Lib/General/NumberTheory/CMFields.lean
  - Lib/ClassField/Places/GaloisDefs.lean
  - Lib/Adelic/Adeles/Basic.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---

## CM fields in the argument

This chapter opens Volume 3. It gives the background in algebraic number theory for the fields that the source uses: the imaginary quadratic field $K$, the CM fields that contain it, the cyclotomic extensions of $K$, the towers of fields that the proof builds, and the places of all these fields. Each part has three steps. First comes the classical theory, with a precise citation. Then comes the form in which the source states it, with its own definitions. Last comes a `Formalization` remark on each difference between the two, and on what the argument uses.

### Where the chapter sits

The plan of the proof is in [the theorem and the plan](/chapter/theorem-and-plan/). The argument fixes parameters $(q_0, d)$, an imaginary quadratic field $K = \mathbb{Q}(\sqrt{-d})$ and, for each $s \ge 0$, a cyclotomic extension $E = K(\zeta)$ with $\zeta$ of order $q_1$. [Fields, places and twists](/chapter/fields-places-twists/) in Volume 1 defines these objects and states the facts about them that the outline uses. This chapter is the background of that chapter. It uses the same notation, and it does not repeat the statements that are there. Where it needs one of them, it links to it.

The next chapter, [class field theory](/chapter/class-field-theory/), builds on the places of this chapter. It uses the valuation subrings of $\bar{\mathbb{Q}}$, the Frobenius elements, the decomposition and inertia groups and the finite ideles, all of which are defined here.

### Why CM fields

Every number field in the argument is a CM field. There are three reasons, and each one is visible in the source.

1. The automorphic objects of the proof live on unitary groups $U(n)$ over $E$, relative to the quadratic extension $E / E^+$. This needs an involution of $E$ with a totally real fixed field, and that is complex conjugation on a CM field.
2. A CM field is totally complex. So every infinite place of $E$ is complex, and the product $\prod_{v \mid \infty} E_v$ is a product of copies of $\mathbb{C}$. The source defines the adeles of $E$ with this product (Section 5). The definition is correct only because $E$ is totally complex.
3. On a CM field, complex conjugation commutes with every embedding into $\mathbb{C}$. So one element $\bar x \in E$ is the complex conjugate of $x$ under all embeddings at once. The source uses this to define conjugation on $\mathcal{O}_E$, on the finite places and on the finite adeles.

The base change steps of the argument make new fields from $E$: fixed fields of automorphisms, and fields $E[X]/(P)$ for polynomials $P$ whose complex roots all have the same absolute value. The source must show that these fields are CM again. Section 3 gives its two criteria.

### What the chapter contains

Section 2 treats the imaginary quadratic field $K$. Section 3 treats CM fields: it states the definition of Mathlib and the two CM criteria of the source. Section 4 treats the cyclotomic extensions of $K$ and the towers. Section 5 treats the infinite places, the choice of embeddings and the adeles. Section 6 treats the finite places: the primes of $\mathcal{O}_E$, their conjugates, and the places of $\bar{\mathbb{Q}}$ as valuation subrings, with decomposition groups, inertia groups and Frobenius elements. Section 7 treats root discriminants and the finite ideles. Section 8 has exercises and notes.

### The sketch

The classical theory and the source agree on the mathematics, but the source makes four choices that a reader must know.

1. **The field E is abstract.** The field $K$ is a subfield of $\mathbb{C}$. The field $E$ is not. It is Mathlib's `CyclotomicField q₁ K`, and the embeddings of $E$ into $\mathbb{C}$ are chosen.
2. **Φ is the set of infinite places.** In the classical theory, a CM type of $E$ is a set of embeddings $E \to \mathbb{C}$, one from each pair of conjugate embeddings. The source writes $\Phi$ for the set of infinite places of $E$, and it fixes one embedding for each place with the class `New.PlaceEmbedding`. The pair of the two is a CM type.
3. **Places above are valuation subrings.** A place of $\bar{\mathbb{Q}}$ above a prime $v$ of a number field is a valuation subring $A$ of the fixed algebraic closure $\Omega = \bar{\mathbb{Q}}$, with the property `New.IsPlaceOver A v`. The decomposition field of $A$ is a henselian local field. It is not complete.
4. **Class field theory uses finite ideles.** The source defines the adeles as $(\prod_{v \mid \infty} \mathbb{C}) \times \mathbb{A}_{E,f}$, and its class field theory works with $\mathbb{A}_{E,f}^\times$ and with totally positive elements.

None of these choices changes a theorem that the argument uses, but each one changes how the theorem is stated. The remarks of the chapter say where.

### Conventions

Number fields are of characteristic $0$ and finite over $\mathbb{Q}$. For a number field $F$, $\mathcal{O}_F$ is its ring of integers, $d_F$ its discriminant and $\mathrm{rd}_F = |d_F|^{1/[F:\mathbb{Q}]}$ its root discriminant. A finite place of $F$ is a nonzero prime ideal $w$ of $\mathcal{O}_F$, and $q_w = \# \mathcal{O}_F / w$ is the order of its residue field. For a CM field $E$, $E^+$ is the maximal totally real subfield and $x \mapsto \bar x$ is complex conjugation. The letter $\Omega$ is the algebraic closure of $\mathbb{Q}$ that the source fixes (`New.Ω` in Lib/ClassField/Places/GaloisDefs.lean), not the number $\Omega$ of Volume 1, chapter 6. Where the two could meet, this chapter writes $\bar{\mathbb{Q}}$ for the field.

The parameters are as in [the parameters](/chapter/fields-places-twists/): $18480 \mid q_0$, $d$ is a prime with $q_0 \mid 2(d+1)$ and $q_0 \nmid d + 1$, so $d \equiv 7 \pmod 8$. For $s \ge 0$, $\mathrm{towerDeg}(s) = 3^{c(s)} 2^s$ with $c(s) = \lfloor \log_3 s \rfloor + 5$, and $q_1 = q_0 \cdot \mathrm{towerDeg}(s)$. The field $E = K(\zeta)$ has $\zeta$ of order $q_1$, and $f = \# \Phi = \mathrm{towerDeg}(s) \varphi(q_0)$ is the number of its infinite places.

The source states its results for a general number field where it can, and for the field $E$ of the parameters only where it must. This chapter follows it. A result stated for a CM field $E$ applies to the field $E$ of the parameters, since that field is CM (Section 4).
