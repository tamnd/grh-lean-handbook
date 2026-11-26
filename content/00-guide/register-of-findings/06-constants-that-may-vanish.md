---
title: Constants that may vanish
lean:
  - New/UpperBound/Seesaw/SeesawIdentity.lean
  - New/Determinant/Exchange/OneSquare.lean
  - New/Determinant/Exchange/TheoremForPartners.lean
  - Lib/SiegelWeil/Tower/LargeSideConstantTerm.lean
  - New/Determinant/Chain/Moduli.lean
  - New/Determinant/Chain/NormOfChain.lean
  - New/OneLift/LiftVolumeHeight.lean
  - New/Spanning/SecondMoment/SpanningTheorem.lean
  - New/Reduction/ShortAndEnough.lean
  - Lib/GLn/Branching/IntegralMap.lean
  - Lib/Weil/CompactLift/DefiniteThetaLift.lean
  - Lib/CM/Sigma/Basic.lean
  - New/Congruences/GaloisRepresentations/SelmerHypotheses.lean
  - New/OneLift/HeckeValues/TwistedRatio.lean
  - New/Determinant/Chain/TriangleNorms.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Constants that may vanish

Many theorems of the source have the form "there is a constant $c$ with $X = cY$". Such a theorem is useful when $c \neq 0$ and $Y \neq 0$, because then it says that $X \neq 0$. But the theorem can hold in a trivial way. If $X = 0$ and $Y = 0$, then $X = cY$ for every $c$. And if the theorem does not say that $c \neq 0$, then it holds with $c = 0$ for every $X = 0$. A reader who reads such a theorem as a proof that $X$ is nonzero reads too much into it.

The source has several theorems of this form. For each one, the register asks two questions. Does the statement exclude the trivial case? And if it does not, where does the source prove the nonvanishing that the argument needs? The rows below give the answers that the source shows. Where the source does not show an answer, the row is open.

### The constants

| ID | File and line | Finding | Effect on the meaning | Chapter |
|---|---|---|---|---|
| F-068, open | [New/UpperBound/Seesaw/SeesawIdentity.lean:624](lean:New/UpperBound/Seesaw/SeesawIdentity.lean#L624), 630-631; `grh/GUIDE.md:57` | `seesaw_identity` gives a unit $c$ of `ℂˣ`. The proof sets $u = 1$ when the natural constant $c_0 C / d$ is $0$ (the comment at lines 630-631). Then the side of the datum is $0$. The guide says that the theorem "does not say that it is nonzero". | The unit $c$ is a real unit, but the identity can be trivial. Nonvanishing of the lower chain must come from elsewhere. | [seesaw-identity-2](/chapter/seesaw-identity-2/), [reading-the-lean](/chapter/reading-the-lean/) |
| F-069, open | [New/Determinant/Exchange/OneSquare.lean:16](lean:New/Determinant/Exchange/OneSquare.lean#L16)-17, 42, 965; `grh/GUIDE.md:61` | In `one_square_identity_of_isEdgeFamily` (line 965) the factor $\kappa$ is not computed and is not shown to be nonzero. Only $c \neq 0$ is given. | If $\kappa = 0$, the square law is trivial. The nonvanishing must come from the chain (F-037). | [seesaw-squares](/chapter/seesaw-squares/) |
| F-070, explained | [New/Determinant/Exchange/TheoremForPartners.lean:1051](lean:New/Determinant/Exchange/TheoremForPartners.lean#L1051), 1073-1074; [Lib/SiegelWeil/Tower/LargeSideConstantTerm.lean:861](lean:Lib/SiegelWeil/Tower/LargeSideConstantTerm.lean#L861) | In `exchange_identity` the constant $C$ is not computed. The statement gives $0 < C$, and $C$ times the L-values is nonzero, so $c \neq 0$, since the square of its norm is $C$ times L-values. The constant term of `LargeSideConstantTerm` is $\gamma$ times `thetaLarge`, with the norm of $\gamma$ equal to $C$ times an L-value and $C > 0$. | Only the norm of $c$ is known, not $c$. The factor $\gamma$ vanishes only where the L-value vanishes. | [exchange-identity-2](/chapter/exchange-identity-2/), [rallis-inner-product](/chapter/rallis-inner-product/) |
| F-071, explained | [New/Determinant/Chain/Moduli.lean:131](lean:New/Determinant/Chain/Moduli.lean#L131)-134; [New/Determinant/Chain/NormOfChain.lean:303](lean:New/Determinant/Chain/NormOfChain.lean#L303)-306 | `HasAbsUpToNormPower` allows $C = 0$, and then $c$ is $0$ for all twists. `exists_adjoint_chain_comp_eq_smul_rallisProduct` gives $0 < C$. | Nonvanishing comes back in the theorem on the chain. | [chain-determinant](/chapter/chain-determinant/) |
| F-072, explained | [New/OneLift/LiftVolumeHeight.lean:172](lean:New/OneLift/LiftVolumeHeight.lean#L172), 175, 554-556; [New/Spanning/SecondMoment/SpanningTheorem.lean:307](lean:New/Spanning/SecondMoment/SpanningTheorem.lean#L307); [New/Reduction/ShortAndEnough.lean:403](lean:New/Reduction/ShortAndEnough.lean#L403) | `IsComparisonOperator` has a field `ratio_ne_zero`. It is proved in `isComparisonOperator_comparisonOp` by `twistFactor_ne_zero`. `finrank_targetForms_ne_zero` proves that the space of target forms is nonzero, and `targetDim_pos` uses it. | The division in the ratio is safe at these places. | [lift-volume-height](/chapter/lift-volume-height/), [proof-of-theorem-b](/chapter/proof-of-theorem-b/) |
| F-073, open | [Lib/GLn/Branching/IntegralMap.lean:39](lean:Lib/GLn/Branching/IntegralMap.lean#L39)-40 | The branching matrix is equivariant and bounded. The file says: "That it is non-zero is not part of the statement." | The book must find where its nonvanishing is used and where it is proved. | [weyl-modules](/chapter/weyl-modules/) |
| F-074, open | [Lib/Weil/CompactLift/DefiniteThetaLift.lean:193](lean:Lib/Weil/CompactLift/DefiniteThetaLift.lean#L193), 198 | `exists_lift_ofAlgForm_eq_smul` gives some $\beta$ (line 198) with the lift equal to $\beta$ divided by an index, times a form. $\beta$ is not shown to be nonzero. | The same question as F-073: where the argument needs $\beta \neq 0$, and where it proves it. | [theta-lifts-seesaw](/chapter/theta-lifts-seesaw/) |
| F-075, explained | [Lib/CM/Sigma/Basic.lean:690](lean:Lib/CM/Sigma/Basic.lean#L690)-694; [New/Congruences/GaloisRepresentations/SelmerHypotheses.lean:307](lean:New/Congruences/GaloisRepresentations/SelmerHypotheses.lean#L307)-308 | For $d = 0$ the conditions of `CMLattice` are void. `twistError` adds $(1/2)^{\ell}$, so it is never $0$. | A reader must not use the case $d = 0$. The extra term makes a sum over all primes converge, with positive terms. | [cm-elliptic-curves](/chapter/cm-elliptic-curves/), [regular-families-plan](/chapter/regular-families-plan/) |
| F-120, explained | [New/OneLift/HeckeValues/TwistedRatio.lean:260](lean:New/OneLift/HeckeValues/TwistedRatio.lean#L260) | `CriticalPair.ratio_ne_zero` is proved from `HasWeight.L_ne_zero`, the nonvanishing of the L-values. It is not proved from `algPart_pos`. | Cite `HasWeight.L_ne_zero` as the place where the nonvanishing of the ratio comes back. | [hecke-values](/chapter/hecke-values/) |
| F-121, explained | [New/Determinant/Chain/TriangleNorms.lean:390](lean:New/Determinant/Chain/TriangleNorms.lean#L390), 370 | `IsTriangle.ne_zero_of_squareCommutes` (line 390) is never applied in the source. Only `ne_zero_of_chainCommutes` (line 370) is used. | The book must not explain the form with squares as a step of the proof. The nonvanishing of the proof comes from the form with chains. | [chain-determinant](/chapter/chain-determinant/) |

### Where the nonvanishing comes back

The explained rows show three ways in which the source recovers nonvanishing.

The first way is a positive constant in the statement. In F-070 the statement of `exchange_identity` gives $0 < C$, and the norm of the constant is $C$ times L-values that the statement also gives as nonzero. In F-071 the predicate `HasAbsUpToNormPower` allows $C = 0$, but the theorem on the chain, which is the one the proof uses, gives $0 < C$. A reader who meets the predicate alone must not assume that $C$ is positive, and a reader who meets the theorem can.

The second way is a field of a structure. In F-072 the field `ratio_ne_zero` of `IsComparisonOperator` asks the nonvanishing, and a lemma proves the field for the operator of the proof. In F-120 the ratio of a critical pair is nonzero because the L-values are nonzero, which is a field of `HasWeight`.

The third way is injectivity. In F-037 and F-121 the factor of a chain is nonzero because the maps of the chain are injective. The source has two lemmas for this, one for squares and one for chains, and only the one for chains is used.

### The open rows

Four rows are open: F-068, F-069, F-073 and F-074. Each is a constant or a factor that a theorem gives with no claim that it is nonzero. In each case the theorem is true as stated, if the reported checks hold. The open question is where the argument uses the nonvanishing, and where it proves it.

The case F-068 is the most visible, because the docstring of `seesawConst` calls it "a non-zero constant" (F-110 in Section 8). The constant is a unit, so the docstring is true. But the proof of `seesaw_identity` replaces the natural constant by $1$ when the natural constant is $0$, and then both sides of the identity are $0$. So the identity, with its unit, does not show that the lower chain of a Poincaré series is nonzero. The plan of the book says that the nonvanishing comes back on the side of the determinant. A chapter of Volume 9 must show where, or leave the row open.

The case F-069 is of the same kind. The factor $\kappa$ of the one square identity is not computed. If it were $0$, the square law would say nothing. The research notes trace the nonvanishing to the injectivity argument of F-037, but F-121 shows that the lemma for squares is not applied. So the path from the one square identity to a nonzero determinant must go through the form with chains. A chapter of Volume 11 must trace it.

The cases F-073 and F-074 are in `Lib`. The branching matrix and the factor $\beta$ of a definite theta lift are not shown to be nonzero where they are defined. The file of F-073 says so in words. A chapter of Volume 5 or Volume 6 must find the use, and the register records the answer here.
