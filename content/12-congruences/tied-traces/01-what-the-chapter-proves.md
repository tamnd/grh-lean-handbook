---
title: What the chapter proves
lean:
  - New/Congruences/Selmer/AuxiliaryPrimes.lean
  - New/Congruences/FirstOrder/EvenClasses.lean
  - New/Congruences/FirstOrder/TateTwistCocycles.lean
  - New/Congruences/FirstOrder/OnePrime.lean
  - New/Congruences/FirstOrder/TiedTraces.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter supplies the local tools for two steps of the argument. The first step makes the Selmer side small: it chooses auxiliary primes and proves that cocycles of the Tate twists $(O/\ell^\nu)(-e)$ have a small *triangle cost*. The second step works on the automorphic side: it computes norms and first-order terms at one auxiliary prime and relates the traces of Galois representations to Hecke operators at that prime. The chapter does not assemble these tools. [Auxiliary primes and first-order deformations](/chapter/first-order-deformations/) and [Tied Selmer groups and the Greenberg-Wiles count](/chapter/tied-selmer-groups/) do that.

The chapter has five parts, one for each Lean file.

1. *Auxiliary primes.* Chebotarev's theorem gives a prime $P$ of the CM field $E$ of prime norm, with a Frobenius element near a prescribed Galois element and a character $\chi$ to $\mathbb{Z}/\ell^N$ that is ramified only at $P$, sends the tame generator at $P$ to $1$ and comes from the norm-one torus. Sets of such primes, with slopes, give the *tie relations* $z(\gamma) = s \cdot z(\varphi)$ on cocycles.
2. *Even classes.* These are the cocycles in $(O/\ell^\nu)(-e)$ that are invariant under conjugation by complex conjugation and satisfy a local condition above $\ell$. A *triangle of primes* is a family of tame generators that cuts them down step by step. The file EvenClasses defines both, but [Auxiliary primes and first-order deformations](/chapter/first-order-deformations/) states them, because it constructs the triangle. This chapter recalls them in one line each and states the rest of the file.
3. *Cocycles of Tate twists.* A triangle of primes gives the triangle cost of [Fitting ideals and the triangle cost](/chapter/ribet-elements/#fitting-ideals-and-the-triangle-cost), with the length of the odd classes $Ш_{\mathrm{odd}}$ and a local loss as the bound.
4. *Norms at one prime.* For a finite group $H$ acting on a ring, the norm $\sum_h h$ and a first-order term $\partial$ satisfy congruences. These give products $\prod_j(\mathrm{Nm}_j + X_j\,\partial_j)$ whose coefficients factor through norms.
5. *Tied traces.* At a Taylor-Wiles place, the trace of a Galois representation at the tame generator is the action of a diamond operator, and the trace at the Frobenius element is the action of a Hecke operator $U$. This is the dictionary that lets the next chapter turn tie relations into Hecke operators.

### The place of the chapter in the argument

[The chain of the proof](/chapter/regular-families-plan/#the-chain-of-the-proof) lists this chapter as chapter 4. It depends on [Pseudocharacters, Fitting ideals and Ribet elements](/chapter/ribet-elements/), because its main result about cocycles has the form of the property `HasTriangleCost` defined there.

Later chapters use it as follows.

- [Auxiliary primes and first-order deformations](/chapter/first-order-deformations/) builds triangles of primes (the file TrianglePrimes), Kummer maps on even classes (KummerMaps), and the deformed norm family at the auxiliary places (AuxiliaryPrimeTie). The last uses the norms of part 4 and the dictionary of part 5.
- [Tied Selmer groups and the Greenberg-Wiles count](/chapter/tied-selmer-groups/) uses the auxiliary primes and the tie relations of part 1 in the files SelmerData, Count, OneSystem, Mirror, Untied and Descent.
- [Stickelberger systems and the twisting theorem](/chapter/twisting-theorem/) uses part 1 in its files Line and StickelbergerLine, and part 2 in TwistingTheorem.
- [From a congruence to a Selmer class](/chapter/denominator-bound/) uses parts 2 and 3 in TraceRelations and DenominatorBound.

### One forward reference

The file TateTwistCocycles imports FittingBlock of chapter 2. FittingBlock imports the file LocalLoss/Basic, which [`volume.yaml`](/chapter/regular-families-plan/#the-map-of-the-files) puts in the later chapter [The main summands of the attached Galois representations](/chapter/main-summands/). This chapter uses one definition from it, the set `crysRelations` of linear relations that hold on the crystalline cocycles above $\ell$. [Even classes and cocycles of Tate twists](/chapter/tied-traces/#even-classes-and-cocycles-of-tate-twists) states this definition once and links forward. No other result of a later chapter is used.

### Notation

Throughout, $\ell$ is a prime and $\Omega$ is the algebraic closure of $\mathbb{Q}$. The field $E \subseteq \Omega$ is a CM field. In parts 2 and 3 it contains a primitive $5040$-th root of unity (the class `New.CMFieldWithRoot5040`). Write $G = \mathrm{Gal}(\Omega/E)$, $c$ for the chosen complex conjugation and $g^c = cgc$ for the map `New.conjGal`. Write
$$\iota_b(g) = \begin{cases} g & b = \text{true}, \\ (g^c)^{-1} & b = \text{false} \end{cases}$$
for `New.idOrConjInv`. If $g$ is in an inertia group at a place over $P$, then $(g^c)^{-1}$ is in an inertia group at a place over $\bar P$. So $\iota_b$ moves statements at $P$ to statements at $\bar P$.

The letter $O$ is a coefficient ring, that is, the ring of integers of a finite Galois extension of $\mathbb{Q}_\ell$ in $\bar{\mathbb{Q}}_\ell$. The character $\mathrm{cyc}$ is the $\ell$-adic cyclotomic character, and $\mathrm{cyc}_N$ is its reduction modulo $N$. The Tate twist $O(-e)$ is $\mathrm{cyc}^{-e}$, written as $1 \times 1$ matrices (`New.Selmer.tateTwist`). For a representation $\rho$, a set $S$ of places and a set $L$ of linear relations, $\mathrm{Sel}(\rho, S, L, B)$ is the module of locally constant cocycles with values in $B$ that are unramified off $S$ and obey $L$ (`New.selmerModule`, from [Building the representations](/chapter/building-representations/)).

### A sketch

The Selmer side needs this. Ribet's element of chapter 2 is small only if each character $O(-e)$ has a small triangle cost. A triangle cost needs places $w_j$ with tame generators $\tau_j$ such that a cocycle that agrees at $\tau_i$ and $(\tau_i^c)^{-1}$ for $i < j$ also agrees at $\tau_j$ and $(\tau_j^c)^{-1}$, up to a bounded power of $\ell$. A cocycle $z$ agrees at $\tau$ and $(\tau^c)^{-1}$ exactly when its even part $z + z \circ \mathrm{conjGal}$ is zero at $\tau$. So the condition is a statement about even classes. This is the reason for part 2. The cost of what is left after the triangle is the odd part $z^c - z$, which lies in $Ш_{\mathrm{odd}}$, and the part of $z$ that is not crystalline above $\ell$. This is part 3.

The automorphic side needs this. The tie relation at a place $v$ says that the cocycle at $\gamma_v$ is $s_v$ times its value at $\varphi_v$. In terms of traces it compares $\mathrm{tr}((\gamma_v - 1)g)$ with $X_v\,\mathrm{tr}((\varphi_v - 1)g)$. Part 5 turns the first trace into a diamond operator and the second into a Hecke operator. Part 4 is the algebra that makes the product of the operators at all places factor through the base level, up to a power of an operator $\delta$ and modulo $\ell^\nu/(2n!)$.

The source claims these results. Lean accepts them, if the reported checks hold. The chapter reports what the declarations state and how the proofs go.
