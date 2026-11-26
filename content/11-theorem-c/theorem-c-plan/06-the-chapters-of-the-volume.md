---
title: The chapters of the volume
lean:
  - New/Determinant/Twist/LongForms.lean
  - New/OneLift/LiftVolumeHeight.lean
  - New/OneLift/HeckeValues/TwistedValueHeights.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapters of the volume

This section is a map of Volume 11: a diagram of the dependencies, one paragraph on each chapter, and the results taken from other volumes. The dependencies are read from the imports of the source files.

### The diagram

An arrow $A \to B$ means that chapter $B$ uses a result of chapter $A$. The numbers are the places of the chapters in the volume. Every chapter uses chapter 1, and chapter 3 is used by almost every later chapter, so these arrows are not drawn.

```text
 2 twists --------+-----------------------------+
                  |                             |
 4 exchange-1     |   12 false-lifts            |
     |            |        |                    |
 5 exchange-2     |   13 comparison-1           |
     |            |     |          |            |
 6 squares        |     v          v            |
     |            |  10 hecke   14 comparison-2 |
     |            |     ^  |       |            |
 7 chain <--------+     |  +---+   |            |
     |               11 sharp  v   v            |
 8 grids                   15 lift-volume <-----+
     |                          |
 9 deep-level                   |
     |                          |
     +------> 16 proof <--------+
```

The volume has two branches. The left branch, chapters 4 to 9, treats the chain of $m$ lifts: its volume and the auxiliary forms. The right branch, chapters 10 to 15, treats one lift at a time: its Hecke values and its denominators. Chapter 2 feeds both branches: chapters 7, 10, 15 and 16 use it. Chapter 16 joins the branches, and it also uses chapter 7 and the existence theorem of Volume 12.

### One paragraph on each chapter

1. [Theorem C and the height argument](/chapter/theorem-c-plan/). This chapter.

2. [Twists, critical pairs and regular families](/chapter/twists-critical-pairs/). This chapter defines the $m$-fold twists $\vartheta$ and their sets $Q$, the critical pairs $(\nu, z)$, the ratio of a pair, and the regular families of Section 4. It states the existence of regular families, which Volume 12 proves, and proves that the ratio is not zero.

3. [Single theta lifts and their norms](/chapter/single-theta-lifts/). This chapter defines the $j$-th single lift from forms on $W_j$ to forms on a definite space of rank $r + t$. It proves that the lift is injective, by Rallis' inner product formula for a sharp block datum.

4. [The exchange identity, part 1](/chapter/exchange-identity-1/). This chapter defines matched functions and proves the exchange identity for partners, with the constant of Section 5.

5. [The exchange identity, part 2](/chapter/exchange-identity-2/). This chapter reduces the general exchange to the case of the stable range by removing hyperbolic planes.

6. [Seesaw squares](/chapter/seesaw-squares/). This chapter applies the exchange to a square of four spaces and gets the square law with a constant $\kappa/c$. Section 5 explains why $\kappa$ may vanish.

7. [The chain determinant and its factorization](/chapter/chain-determinant/). This chapter builds the triangle of lifts, proves that chains are injective, and proves the operator identity $\Theta_\vartheta^*\Theta_\vartheta = c(\vartheta)c_Q^m R(\vartheta)$.

8. [Grids, paths and turns](/chapter/grids-paths-turns/). Paths through a grid of squares give the auxiliary forms, and each turn of a path costs a turn ratio of Hecke values. The grid gives the scalar $\gamma(\vartheta)$ of the auxiliary forms.

9. [Deep level Poincaré series and spanning forms](/chapter/deep-level-poincare/). This chapter shows that forms of deep level with short lifts span, by Poincaré series and their periods. With chapter 8 it proves the theorem on auxiliary forms.

10. [Hecke values of character lifts](/chapter/hecke-values/). This chapter relates the Hecke values of a twist to $L$-values. It proves that the algebraic part of a critical pair is positive, and it bounds the height of the inverse ratios of Hecke values by $10 m x_1 + k(6\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount})$. It uses the false lifts, the three exchanges of chapter 13 and the sharpness of chapter 11.

11. [The divisibility is sharp](/chapter/sharpness/). This chapter shows that the divisibility bound of the Taylor coefficients is attained: at every prime $p$, some Taylor coefficient of an indicator datum has valuation at most $S_p + v(t)$, for one number $t \neq 0$ with small conjugates. This gives the term $-\mathrm{directionAmount}$ its full size.

12. [False lifts](/chapter/false-lifts/). This chapter defines point forms and the false lifts: forms in the complement of the lifts that satisfy the conditions on a lift. It proves that the projection to the lifts does not increase norms on forms orthogonal to the false lifts.

13. [The comparison operator, part 1](/chapter/comparison-operator-1/). This chapter builds the gluing map from forms on $V^\circ$ to forms on $V_j$ and computes its adjoint by three exchanges. These give the algebraic properties of the comparison operator.

14. [The comparison operator, part 2](/chapter/comparison-operator-2/). This chapter solves the basis problem for the forms on $V^\circ$ and bounds the theta kernels. This gives the archimedean bound for $U_1$, property 5 of Section 4.

15. [The height of one lift determinant](/chapter/lift-volume-height/). This chapter proves that the operators $U_\vartheta$ are comparison operators, and proves the height bound $d\,k(\log b\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount})$ for $Z_j(1)/Z_j(\theta(\iota))$.

16. [The proof of Theorem C](/chapter/proof-of-theorem-c/). This chapter gives the proof of Section 3 in full: the theorem on a twist for each prime, the cost of completion, and the inverse ratio lemma.

### Prerequisites from other volumes

Volume 11 uses Volume 6 directly, and Volumes 7 and 8 only through Volume 12.

From Volume 6 the volume uses the following.

- [The Weil representation from a vacuum](/chapter/weil-representation/): the Fock model and the mixed models of the theta kernels.
- [Theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/): dual pairs, definite lifts and the seesaw identity.
- [Bessel periods and one step of unfolding](/chapter/bessel-periods/): the periods used for the false lifts and the comparison operator.
- [The Siegel-Weil formula](/chapter/siegel-weil/): the formula in Weil's range, used for the constants of the exchange.
- [Doubling and the Rallis inner product formula](/chapter/rallis-inner-product/): the Rallis inner product formula and the tower. The injectivity of a single lift and the operator identity of the chain determinant rest on it.

From Volume 12 the volume uses one theorem, the existence of regular families of Section 4. [Regular families: the plan](/chapter/regular-families-plan/) explains the denominator budget, and [the proof of the existence of regular families](/chapter/proof-of-regular-families/) gives the proof. Its two main steps are in [from a congruence to a Selmer class](/chapter/denominator-bound/) and [the twisting theorem](/chapter/twisting-theorem/). The bounds for the Hecke values in chapter 10 also use the Selmer hypotheses of Volume 12.

From Volume 7, Volume 12 uses [Kisin frames and limits](/chapter/kisin-frames/), [period rings and crystalline representations](/chapter/period-rings/), and [Fitting ideals, lengths and coefficient rings](/chapter/fitting-ideals/).

From Volume 8, Volume 12 uses [what attached means](/chapter/attached-representations/) and [building the representations](/chapter/building-representations/): the Galois representations attached to the forms.
