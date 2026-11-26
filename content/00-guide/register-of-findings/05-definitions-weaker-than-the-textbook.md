---
title: Definitions weaker than the textbook
lean:
  - Lib/GaloisRep/Main/AttachedRepresentations.lean
  - Lib/GaloisRep/Main/Defs.lean
  - Lib/GaloisRep/Main/LocalConditions.lean
  - Lib/Cohomology/Etale/Basic.lean
  - Lib/Cohomology/Etale/FilteredLimits.lean
  - Lib/Cohomology/WoodsHole.lean
  - Lib/PadicComparison/HodgeTate/PeriodMap.lean
  - Lib/PadicHodge/Crystalline/Basic.lean
  - Lib/Adelic/Adeles/Basic.lean
  - Lib/Adelic/Unitary/Defs.lean
  - New/Spanning/SecondMoment/FewTranslates.lean
  - New/Reduction/Lattices/Colength.lean
  - Lib/GaloisRep/Main/SelmerModules.lean
  - Lib/Cyclotomic/OddSha.lean
  - Lib/Shimura/AbelianScheme/Basic.lean
  - Lib/General/Geometry/LineBundles.lean
  - Lib/General/Geometry/EtaleCharts.lean
  - Lib/General/LinearAlgebra/IntegralLattices.lean
  - Lib/CM/ChowlaSelberg.lean
  - Lib/LocalGL/Shintani/CosetDescent.lean
  - Lib/Analytic/Primes.lean
  - Lib/Analytic/QuadraticTwist.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Definitions weaker than the textbook

The folder `Lib` of the source holds the background theories. The guide of the source says that `Lib` proves parts of standard theories, often in a weaker form and with its own definitions. So a name of `Lib` such as `Attached`, `IsAbelianScheme` or `IsCrystalline` does not always mean what it means in a textbook. Often it means less. This is not an error of the source. A weaker definition is enough when the proof uses only the weaker property, and a weaker definition is shorter to state and to prove. But a reader who reads the name as the textbook notion can believe that the source proves more than it does.

This section lists the definitions where the difference matters. The rule for the book is the same in each case. A chapter of the book that uses one of these definitions states the definition of the source next to the textbook definition, and says which one the proof uses.

### The rows

| ID | File and line | Finding | Effect on the meaning | Chapter |
|---|---|---|---|---|
| F-052, explained | `grh/GUIDE.md:30` | `Lib` proves parts of standard theories, often in a weaker form and with its own definitions. | Each chapter on a theory of `Lib` must state the definition of the source next to the textbook one. | [how-to-read](/chapter/how-to-read/) |
| F-053, open | [Lib/GaloisRep/Main/AttachedRepresentations.lean:62](lean:Lib/GaloisRep/Main/AttachedRepresentations.lean#L62); [Lib/GaloisRep/Main/Defs.lean:209](lean:Lib/GaloisRep/Main/Defs.lean#L209) | `Attached`: for every $\eta > 0$ the coefficients of the characteristic polynomial are within $\eta$ of the Hecke polynomial for "most Frobenius data" (`mostFrobenii`, at `Defs.lean:209`). It is not equality at almost all places. | This is far from the textbook notion of an attached representation. It is not known whether the finite set of excluded data can depend on the twist. | [attached-representations](/chapter/attached-representations/) |
| F-054, explained | [Lib/GaloisRep/Main/LocalConditions.lean:60](lean:Lib/GaloisRep/Main/LocalConditions.lean#L60), 108 | `GalRep` is a bare group homomorphism, with no continuity. Continuity comes only from the field `continuous` of `Attached`. `PolyKillsAt` (line 108) records which polynomials kill an element. There is no monodromy and no Weil-Deligne representation. | Local-global statements are in the "kills" form only, not in the form of an equality of characteristic polynomials. | [attached-representations](/chapter/attached-representations/) |
| F-055, explained | [Lib/Cohomology/Etale/Basic.lean:114](lean:Lib/Cohomology/Etale/Basic.lean#L114); [Lib/Cohomology/Etale/FilteredLimits.lean:42](lean:Lib/Cohomology/Etale/FilteredLimits.lean#L42)-45; [Lib/Cohomology/WoodsHole.lean:49](lean:Lib/Cohomology/WoodsHole.lean#L49)-50 | Cohomology is `Abelian.Ext` of presheaves on test rings. The documents say that its equality with étale cohomology "is neither proved nor used". | Soundness does not need the equality. The claim that `Lib` holds known results needs it. | [cohomology-ext](/chapter/cohomology-ext/) |
| F-056, explained | [Lib/PadicComparison/HodgeTate/PeriodMap.lean:40](lean:Lib/PadicComparison/HodgeTate/PeriodMap.lean#L40)-43; [Lib/PadicHodge/Crystalline/Basic.lean:104](lean:Lib/PadicHodge/Crystalline/Basic.lean#L104)-106 | The Hodge-Tate period map is built, but its bijectivity is not proved. `IsCrystalline` is admissibility for `Bmax`: the fixed periods span `Bmax ⊗ T`. | The book must not call the period map an isomorphism. The period ring is `Bmax`, not the ring $B_{\mathrm{cris}}$ of Fontaine. | [comparison-theorems](/chapter/comparison-theorems/), [period-rings](/chapter/period-rings/) |
| F-057, explained | [Lib/Adelic/Adeles/Basic.lean:98](lean:Lib/Adelic/Adeles/Basic.lean#L98)-100; [Lib/Adelic/Unitary/Defs.lean:496](lean:Lib/Adelic/Unitary/Defs.lean#L496)-498 | `𝔸 E` is one copy of $\mathbb{C}$ for each infinite place, times the finite adeles. It is the adele ring only when $E$ is totally complex. `Space` is a hermitian matrix $J$ with a point $x$ such that $x^{*} J x$ is $\operatorname{diag}(s)$ at the infinite places and $1$ at the finite places. | The name hides a hypothesis on $E$. A space carries a chosen point, unlike a hermitian space of the textbook. | [adeles-hermitian-spaces](/chapter/adeles-hermitian-spaces/) |
| F-058, explained | [Lib/Adelic/Adeles/Basic.lean:406](lean:Lib/Adelic/Adeles/Basic.lean#L406)-416 | `HasPrimitiveRoot5040 E`: the field $E$ contains a primitive root of unity of order $7! = 5040$. The comments call such fields "stably unramified". | The documents give no source for the constant $5040$. | [cm-fields](/chapter/cm-fields/) |
| F-059, open | [New/Spanning/SecondMoment/FewTranslates.lean:151](lean:New/Spanning/SecondMoment/FewTranslates.lean#L151) | `IsNearIsometry` is a lower bound on the Hilbert-Schmidt norm on every subspace. It is not a notion of the operator norm. | The book must compare it with the usual notion of a near isometry. | [few-translates](/chapter/few-translates/), [moments](/chapter/moments/) |
| F-060, explained | [New/Reduction/Lattices/Colength.lean:30](lean:New/Reduction/Lattices/Colength.lean#L30)-36 | `ColengthDvd M N z` needs no bases and no inclusion $N \leq M$. | It reads as a divisibility of colengths only over a valuation ring. | [twisted-lattices](/chapter/twisted-lattices/) |
| F-061, explained | [Lib/GaloisRep/Main/SelmerModules.lean:183](lean:Lib/GaloisRep/Main/SelmerModules.lean#L183); [Lib/Cyclotomic/OddSha.lean:14](lean:Lib/Cyclotomic/OddSha.lean#L14)-17 | `shaOdd` is a module of cocycles, modelled on the odd part of the Tate-Shafarevich group $\mathrm{Sha}^1$. No comparison with $\mathrm{Sha}^1$ is proved. | The Selmer bounds are about this module, not about $\mathrm{Sha}^1$. | [tied-selmer-groups](/chapter/tied-selmer-groups/), [odd-classes](/chapter/odd-classes/) |
| F-062, open | [Lib/Shimura/AbelianScheme/Basic.lean:68](lean:Lib/Shimura/AbelianScheme/Basic.lean#L68)-72; [Lib/General/Geometry/LineBundles.lean:59](lean:Lib/General/Geometry/LineBundles.lean#L59); [Lib/General/Geometry/EtaleCharts.lean:925](lean:Lib/General/Geometry/EtaleCharts.lean#L925) | `IsAbelianScheme` (the class at line 70): smooth, proper, and multiplication by every $m \neq 0$ is surjective. Connected fibres are not stated. `PointFn X` is any rule on points with values in rings, with no compatibility. `IsCharting` is defined through closed classes of functors. | It is not known whether this equals the textbook notion on the bases that the source uses. Line bundles and `Pic` are built by hand on these definitions. | [schemes-through-points](/chapter/schemes-through-points/), [complex-abelian-varieties](/chapter/complex-abelian-varieties/) |
| F-063, explained | [Lib/General/LinearAlgebra/IntegralLattices.lean:254](lean:Lib/General/LinearAlgebra/IntegralLattices.lean#L254)-256 | The Smith normal form over valuation pairs states no divisibility among the diagonal entries. | It is weaker than the Smith form of the textbook. | [elementary-divisors](/chapter/elementary-divisors/) |
| F-064, open | [Lib/CM/ChowlaSelberg.lean:692](lean:Lib/CM/ChowlaSelberg.lean#L692)-696 | `chowla_selberg` gives a number $u$ that is a unit at every $p$-adic place. It does not say that $u$ is algebraic. | It is not known whether `New` needs $u$ to be algebraic. | [cm-elliptic-curves](/chapter/cm-elliptic-curves/), [weighted-prime-remainder](/chapter/weighted-prime-remainder/) |
| F-065, explained | [Lib/LocalGL/Shintani/CosetDescent.lean:99](lean:Lib/LocalGL/Shintani/CosetDescent.lean#L99); `grh/GUIDE.md:54` | The predicate `Lift` is Shintani lifting. The folder `New/Congruences/Lifting` is about $p$-adic Hodge theory. | Two unrelated uses of the word "lift" sit next to the theta lifts. | [notation](/chapter/notation/) |
| F-066, explained | [Lib/Analytic/Primes.lean:22](lean:Lib/Analytic/Primes.lean#L22)-25, 386-389 | The prime theorem of the file finds one prime $p \equiv 1 \bmod M^k$ in a long window, for moduli that are powers of a fixed multiple of $4$. It is proved directly by Newman's method. | It is far weaker than the theorem of Siegel and Walfisz, which the file names. | [primes-in-windows](/chapter/primes-in-windows/) |
| F-067, open | [Lib/Analytic/QuadraticTwist.lean:41](lean:Lib/Analytic/QuadraticTwist.lean#L41)-44, 796 | The zero-density input is a weak form. `exists_entireL_quadTwist_ne_zero` (line 796) finds one prime $d$ of the class with no zeros of the twists in a box. | It is the deepest analytic input of the reduction. Its faithfulness to the cited works is not checked. | [polya-vinogradov](/chapter/polya-vinogradov/) |

### Three patterns

The rows fall into three patterns.

The first pattern is a definition with a hypothesis that its name hides. In F-057 the ring `𝔸 E` is the adele ring of $E$ only when $E$ is totally complex, because it has one copy of $\mathbb{C}$ for each infinite place. The fields of the proof are CM fields, so they are totally complex, and the definition is the right one for them. But a lemma about `𝔸 E` for a field with a real place is a lemma about another ring. In F-060 the predicate `ColengthDvd` reads as a divisibility of colengths only over a valuation ring. In F-065 the word "lift" has three meanings in three folders.

The second pattern is a definition that asks less than the textbook. The notion `Attached` of F-053 is an approximate agreement of characteristic polynomials at most Frobenius data, for every tolerance $\eta$. The textbook asks an exact equality at almost all places. The notion of F-054 has no continuity and no monodromy. The cohomology of F-055 is a cohomology of presheaves on test rings, and no comparison with étale cohomology is proved. The module of F-061 is modelled on the odd part of $\mathrm{Sha}^1$, and no comparison is proved. The Smith form of F-063 has no divisibility chain. The prime theorem of F-066 finds one prime in a long window.

In each case the proof uses only the weaker notion, if the reported checks hold. So the weaker definition is enough for the five theorems. But a statement of `Lib` with such a definition is not the textbook theorem of the same name. A reader who wants to cite a result of `Lib` as a result about the textbook notion must first prove the comparison, and the source does not.

The third pattern is a definition of which it is not known whether it is weaker. In F-062 it is not known whether an abelian scheme in the sense of the source is one in the sense of the textbook, on the bases that the source uses. In F-064 it is not known whether the number $u$ of the Chowla-Selberg formula is algebraic, and whether `New` needs that. In F-067 the zero-density statement is a weak form, and it is not checked against the works of Jutila and Heath-Brown that the file cites. These rows are open.
