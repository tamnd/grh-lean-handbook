---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $f$ be the function on points of $\operatorname{Spec} \mathbb{Z}$ with $f(B, t) = 1$ if $B$ is a field and $f(B, t) = 0$ otherwise. Show that $f$ is not regular on $\operatorname{Spec} \mathbb{Z}$. Then show that every function regular on all of $\operatorname{Spec} \mathbb{Z}$ is the function of an integer.

*Hint.* Use the map $\mathbb{Z} \to \mathbb{Q}$. For the second part, use `New.PointFn.IsRegularOn.exists_ofSection` of Section 2, or evaluate at the identity point.

**Exercise 2.** Let $L$ be a line bundle on $X$. Write down an explicit frame of $L \otimes L^{-1}$, and show that $L \otimes L^{-1}$ and $\mathbf{1}$ have the same class without the frame, by the refinement theorem of Section 3.

*Hint.* The frame is $u_{(i,j)} = g_{ij}$. For the refinement, compare $\mathbf{1} \otimes (L \otimes L^{-1})^{-1}$ with a bundle on the diagonal charts $(i, i)$.

**Exercise 3.** Complete the comparison of Section 3 between `New.Pic X` and $\check{H}^1(X, \mathcal{O}_X^\times)$. Show that the map is well defined, that it is a homomorphism, and that it is injective and surjective. Where do you use that every open cover can be indexed by a type in the universe $0$?

*Hint.* For injectivity, a frame of $L \otimes M^{-1}$ is a $0$-cochain on the common refinement whose coboundary relates the two cocycles. For surjectivity, use `New.PointFn.ofSection` on the overlaps, and check the cocycle condition at points with values in local rings.

**Exercise 4.** On $\mathbb{P}^1 = \mathbb{P}^{\{0,1\}}$, write down the linear system $\mathcal{O}(1)^{\otimes 2}$ of Section 5. List its index set, its charts and its transition functions. Show that two of its four coordinates are equal functions, and find the map to $\mathbb{P}^2$ that removes the repetition.

*Hint.* The index set is $\{0, 1\}^2$. The coordinates $(0, 1)$ and $(1, 0)$ are both the function $x_0 x_1$ in the classical form.

**Exercise 5.** Let $X$ be a scheme over a field of characteristic $l$, and $L = (U_i, g_{ij})$ a line bundle, not a linear system. Prove that $l\,[L] = [F^* L]$ in `New.Pic X`, where $F$ is the absolute Frobenius with $f = 1$.

*Hint.* Follow the proof of Section 6, but compare $F^* L$ with $L^{\otimes l}$ on the overlaps $U_i \cap U_j$ only. Use that $g_{ij}$ is regular on $U_i \cap U_j$.

**Exercise 6.** Let $X$ be an affine scheme with an atlas of dimension $1$ over a noetherian ring $k$, with one chart whose coordinate is $T$. Write down the charts $u_{(i, S)}$ of the proof of `New.Variety.HasAtlas.exists_isCharting` for this chart, and check that their loci cover the field-valued points.

*Hint.* There are two sets $S$: the empty set and the set of the one index. The two charts invert $T$ and $T + 1$.

**Exercise 7.** Let $\xi$ be the family of all complex points of $\mathbb{A}^1_{\mathbb{C}}$ with integer coordinates. Show that it is a separating family. Deduce that a polynomial in $\mathbb{C}[T]$ that vanishes at all integers is zero, from `New.IsSeparatingFamily.pointFn_ext`.

*Hint.* An infinite set of closed points of $\mathbb{A}^1_{\mathbb{C}}$ is dense, because the proper closed subsets are finite.

## Notes and references

For schemes through their functors of points, see Eisenbud and Harris, *The Geometry of Schemes*, Chapter VI. For line bundles, the Picard group and its relation to $H^1(X, \mathcal{O}_X^\times)$, see Hartshorne, *Algebraic Geometry*, Chapter II, Section 6, and Chapter III, Exercises 4.4 and 4.5. Maps to projective space and generating sections are in Hartshorne, Chapter II, Section 7, Theorem 7.1. The Segre and Veronese embeddings are Hartshorne, Chapter I, Exercises 2.14 and 2.12. A proper monomorphism is a closed immersion by EGA IV, Corollaire 18.12.6. Smooth morphisms are locally étale over affine space by EGA IV, Corollaire 17.11.4, and the infinitesimal lifting criterion is in EGA IV, Section 17. Descent along faithfully flat morphisms is in SGA 1, Exposé VIII.

The source treats all of this through points. A function is a rule on ring-valued points, a line bundle is a cocycle of such functions, and a projective embedding is a linear system that separates the points of each chart. The main theorems compare these objects with the sections, morphisms and closed immersions of Mathlib. The cost of the approach is the junk values off the opens, which every definition must control, and the use of `choose` in the gluing steps. In every case in this chapter the chosen objects are determined by a property, so no choice appears in a statement.

The findings of this chapter are the following.

1. The source has no comparison of `New.Pic X` with a Picard group of Mathlib or with $H^1(X, \mathcal{O}_X^\times)$. Section 3 gives an argument, not checked in Lean, that `New.Pic X` is isomorphic to $\check{H}^1(X, \mathcal{O}_X^\times)$. It answers the second half of question Q-63 of the findings of the plan, on every scheme.
2. The tensor power `New.LineBundle.pow` is indexed by ordered tuples, so its coordinates repeat. Its docstring calls it the system of all monomials. The repetition does not affect the results of the source.
3. The theorem on the Frobenius and the Picard group is stated only for linear systems. The general form holds by the same proof.
4. The files of `Lib/General/Geometry` import files of `Lib/Shimura`: `SerreTheorem.lean` imports `Lib/Shimura/ThetaGroup.lean` and `Lib/Shimura/ThetaNormality/NormalGeneration.lean`, and `PointsOfProperSchemes.lean` imports `Lib/Shimura/AbelianScheme/Basic.lean`. So the general part does not come before the Shimura part in the import order.
5. The class `New.Variety.IsCharted` is declared at line 1052 of `Lib/General/Geometry/EtaleCharts.lean`.

Status: drafted by a model. No person has checked this chapter against the Lean source.
