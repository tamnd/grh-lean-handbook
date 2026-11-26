---
title: What the chapter proves
lean:
  - New/Congruences/FirstOrder/TraceRelations.lean
  - New/Congruences/FirstOrder/DenominatorBound.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter proves the bound for denominators of [a model case](/chapter/regular-families-plan/#a-model-case-congruences-and-denominators). Let $Z$ be a space of automorphic forms that is spanned by lifts, and let $y$ be a form that is integral at $\ell$ and orthogonal to the false lifts. The orthogonal projection of $y$ to $Z$ need not be integral. The chapter builds an operator $\Lambda$ on $Z$ that takes every such projection to an integral form, and it bounds the $\ell$-adic valuations of the eigenvalues of $\Lambda$ by
$$\mathrm{liftValuationBound}(\ell, O, \mathrm{ram}, \mathrm{sel}) = \mathrm{sel} + 2t'\,\mathrm{ram} + \#r \cdot \mathrm{loc}_\ell + e_\ell.$$
Here $\mathrm{sel}$ bounds the lengths of the Selmer groups of the lifted Galois representations, $\mathrm{ram}$ bounds the ramification of the twist, $\mathrm{loc}_\ell$ is the local loss above $\ell$ per unit of rank, and $e_\ell$ is an explicit error term.

The idea is Ribet's method. A congruence between a lift and a form that is not a lift gives an extension of Galois representations, and so a Selmer class. If the Selmer group is short, then the congruences are few, and the denominator of the projection is small. The chapter makes each step of this idea quantitative.

### Its place in the plan

The plan of the whole proof is in [the theorem and the plan](/chapter/theorem-and-plan/). Theorem C needs regular families, and [the chain of the proof](/chapter/regular-families-plan/#the-chain-of-the-proof) gives them in five steps. Step 4 is Ribet's method for each space of lifts. It uses three results of this chapter.

- `New.Selmer.exists_operator_ellVal_le_liftValuationBound`, the bound for denominators. [A model case](/chapter/regular-families-plan/#a-model-case-congruences-and-denominators) states it and points here for its proof. The proof is in [the bound for denominators](/chapter/denominator-bound/#the-bound-for-denominators).
- `New.Selmer.exists_operator_det_clearingBound` and `New.Selmer.denominatorLe_clearingBound`, the operator form with the clearing bound $\beta_\ell$. The same section states and proves them.
- The constants $\mathrm{loc}_\ell$, $e_\ell$ and $\beta_\ell$, and the arithmetic lemma that adds them up. [The denominator budget](/chapter/regular-families-plan/#the-denominator-budget) states them. [The constants](/chapter/denominator-bound/#the-constants) states them again and proves the lemmas.

[Ribet's element for Galois representations](/chapter/ribet-elements/#ribets-element-for-galois-representations) imports three results from the file TraceRelations of this chapter: the value $\mathrm{loc}_\ell = 4f\,\mathrm{defect}_\ell$, the value of $e_\ell$, and the cocycle bound. The cocycle bound is `New.Selmer.length_ribetCocyclesVanishingOn_le`, with its proof in [cocycle bounds and local defects](/chapter/denominator-bound/#cocycle-bounds-and-local-defects). The same section and the next one prove the other lemmas of TraceRelations that the theorem `New.Selmer.ribet_columns` uses.

### What it uses

The chapter is the end of Ribet's method to first order. It uses the earlier chapters of this volume as follows.

- [Ribet elements](/chapter/ribet-elements/) gives the theorem `New.Selmer.ribet_columns`: a common Ribet element $d$ for a family of conjugate self-dual representations, with $v_\ell(d) + 2v_\ell(N) \leq \mathrm{liftValuationBound}$.
- [First-order deformations](/chapter/first-order-deformations/) gives the triangle of primes `New.Selmer.exists_isPrimeTriangle`, the root chains of weak lifts, and the theorem `New.Patching.BaseLevel.exists_diagOp_mem_ellIntegralForms`, by which the top coefficient of a Ribet element clears denominators.
- [Tied traces and even classes](/chapter/tied-traces/) gives the triangle cost of a Tate twist and the auxiliary twists.
- [The main summands](/chapter/main-summands/) gives lift settings, representations of a type, main summands, twisted lattices, the Selmer hypothesis and the base data of a label.
- [The local loss at ℓ](/chapter/local-loss/), chapter 9 of this volume, gives the bound for the defect of one summand at one place above $\ell$ and the bound for the relative length of Ribet's cocycles by the dual defect.

Background from Volumes 2 to 8 enters in one line each, with a link, where it is used. No file of this chapter imports a file that `volume.yaml` places in a later chapter of Volume 12.

### Notation

The data $D$ fixes the CM field $E$ with $f$ infinite places, the rank $r$, the number $t = 5r$ of characters, the half gap $h_{\mathrm{gap}} = r^8$ and the two level primes $p_0, p_1$ with product $M$ ([the data and its sizes](/chapter/data-and-sizes/)). The number $N$ is `D.chosenGroupOrder`, the product of the orders of the groups $\mathrm{GL}_{rt}(k_w)$ over the residue fields $k_w$ of the chosen places above $p_0$ and $p_1$. Write $v = v_\ell(N)$. A descent pair $O$ has ranks $\#r < \#n$ and rank difference $t' = \#n - \#r$. A coefficient ring is the ring of integers of a finite Galois extension of $\mathbb{Q}_\ell$ inside $\overline{\mathbb{Q}}_\ell$; "for every large coefficient ring" means along the filter `atTop` of these rings. The valuation $\mathrm{ellVal}$ on $\overline{\mathbb{Q}}_\ell$ has $\mathrm{ellVal}(\ell) = 1$, takes the value $\infty$ at $0$, and replaces negative values by $0$.

### A sketch

The proof has three layers.

1. *Constants and Galois inputs* (Sections 2 to 5). The file TraceRelations fixes the constants. It checks that a trace ideal stays a trace ideal when the conjugate tame generators are added. It chooses lattices that are block diagonal for the main summand and the characters. It bounds the cocycles that the method produces by a crystalline colength plus a Selmer length, and it bounds the crystalline colength by the local defects. It builds the relations at the tame places.
2. *One lift generator* (Sections 6 and 7). The file DenominatorBound picks the auxiliary places of the Taylor-Wiles method, applies `ribet_columns` at these places, and applies the clearing theorem of [first-order deformations](/chapter/first-order-deformations/). The result is an operator $G$ that is diagonal on the lift generators, has a small eigenvalue at one generator $v_0$, and takes projections of integral forms orthogonal to false lifts to integral forms.
3. *All lift generators* (Section 8). A basis of $Z$ of lift generators gives one operator $G_k$ for each basis vector. One integral combination of the $G_k$ has all eigenvalues small. A factor $N$ then gives the determinant bound with $\beta_\ell$.

The source claims these results, and Lean accepts them if the reported checks hold. This chapter explains what the declarations state and how the proofs go.

### How the sections are arranged

Section 2 fixes the constants. Section 3 proves the trace relations and chooses the block diagonal lattices. Section 4 proves the cocycle bound and bounds the local defects. Section 5 builds the tame relations and the cyclotomic generator. Section 6 builds the auxiliary places and the operator at one base system. Section 7 treats false lifts and lift generators, and Section 8 proves the bound for denominators. Section 9 has exercises and notes.
