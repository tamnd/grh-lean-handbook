---
title: What the chapter proves
lean:
  - New/Determinant/Twist/LongForms.lean
  - New/Reduction/MainInequality.lean
decls:
  - New.Data.integral_forms_long
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter is the last chapter of the volume. It assembles Theorem C from the results of chapters 2 to 16 and from the existence theorem of Volume 12. It states Theorem C as Lean states it, and it gives the whole proof. Each input is stated exactly as the source proves it, with a link to the section that proves it. The chapter tracks every constant. Section 6 maps the proof to the declarations of the source, and Section 7 compares the plan of the volume with the source.

[Theorem C and the height argument](/chapter/theorem-c-plan/) gives the motivation, the model case and a short form of the proof. This chapter does not repeat the motivation. It proves in full the steps that the plan only names. All of these steps are in one file, New/Determinant/Twist/LongForms.lean. The chapter [Theorems A, B and C](/chapter/theorems-a-b-c/#theorem-c-long-forms) of Volume 1 also uses this file, and it gives a short form of the same proof.

### The notation

Fix parameters $P$ and admissible data $D$ for $P$. The letters are those of [the data and its sizes](/chapter/data-and-sizes/#the-table-of-sizes).

1. $x$, $x_1$ and $b$ are the three scales, with $x^{10^6} \leq x_1$ and $x_1^{10^6} \leq b$. The number $\log b$ is `D.logB`.
2. $m$ is the number of lifts, $r$ is a rank, $k = r + 1 - m$ and $t = 5r$.
3. $f$ is the number of infinite places of the field, and $a = x b$.
4. $d = D.\mathtt{targetDim}$ is the dimension of the target $D.\mathtt{targetForms}$, the good forms on the space $Y_0$.
5. $\mathrm{err}_0 = D.\mathtt{errorUnit} = f a \log^3 b$.
6. $\mathrm{directionAmount} = \sum_\sigma \bigl(s_\infty(\kappa_\sigma) - s_{\mathrm{fin}}(\kappa_\sigma, \sigma)\bigr)$, the sum over the infinite places $\sigma$ of weight $\kappa_\sigma$ of the jet size less the prime sum ([the prime sums](/chapter/prime-sums/)).
7. $\mathrm{mainAmount} = m\,k\cdot\mathrm{directionAmount}$.
8. $\iota$ runs over the pairs of a prime $\ell$ and an isomorphism $\mathbb{C} \cong \overline{\mathbb{Q}}_\ell$ (`New.PrimePadicIso`). A family indexed by $\iota$ has a height, as in [heights over the isomorphisms with the l-adic numbers](/chapter/twisted-lattices/#heights-over-the-isomorphisms-with-the-l-adic-numbers).
9. $\Theta_\vartheta = D.\Theta\,\vartheta$ is the chain of $m$ lifts for the $m$-fold twist $\vartheta$. Its Gram determinant is the chain determinant $Z(\vartheta)$, and $Z_j(\vartheta)$ is the Gram determinant of the $j$-th single good lift at $\vartheta^j$.
10. The target lattice $D.\mathtt{targetLattice}$ is the twisted lattice of target forms with the maps $\Theta_\vartheta$ ([the target lattice](/chapter/integral-target-forms/#the-target-lattice)).

### The statement

**Theorem (Theorem C, integral forms are long).** Let $y_1, \dots, y_n$ be linearly independent target forms with $(1 - 4/b^2)\,d \leq n$. Suppose that $y$ has index at most $\delta$ and covolume at most $c$ in the target lattice. Then

$$d\,\bigl(\mathrm{mainAmount} - 3 f a\log^4 b\bigr) \leq c + 2\delta.$$

Lean: `New.Data.integral_forms_long` (New/Determinant/Twist/LongForms.lean).

The index and the covolume are those of [twisted lattices, index and covolume](/chapter/twisted-lattices/#twisted-lattices-index-and-covolume). Section 2 recalls them. Section 5 gives the proof.

**Remark (Formalization).** The statement has no sign condition on $c$ or $\delta$. The index condition forces $\delta \geq 0$: its sum over the empty set of primes is $0 \leq \delta$. The statement does not say $n \leq d$. This follows from the linear independence. The theorem is about one family of data $D$, with all sizes fixed by $D$. No constant of the statement is chosen in the proof.

### Where the hypotheses come from

Theorem C is used once in the source, in the proof of the main inequality `New.star_inequality` (New/Reduction/MainInequality.lean), at [line 134](lean:New/Reduction/MainInequality.lean#L134). The chapter [the main inequality](/chapter/main-inequality/#the-main-inequality) of Volume 1 gives that proof. There the four hypotheses have these sources.

1. Theorem B (`New.Data.enough_forms`) gives a finite set $t$ of elements of the finite group and the bound $(1 - 4/b^2)\,d \leq \dim\sum_{g \in t}\operatorname{range}(g\mathfrak{p})$. The proof takes a basis $y$ of this sum among the images of short integral forms. This gives the linear independence and the hypothesis on $n$.
2. Theorem A, part (b), bounds the index of these images. The proof gets index at most $\delta = d\cdot 10\log(1 + 2b^2)\,\mathrm{err}_0$ from `New.Data.indexLe_normalizedPoincare` and the count $\#t\cdot\dim\mathrm{src} \leq 5\,d\log(1 + 2b^2)$ of Theorem B.
3. Theorem A, part (a), bounds the length of the short forms. Each $y_i$ has $\|\Theta_1 y_i\|_\sigma^2 \leq \exp(L)$ with $L = \mathrm{mainAmount} - m\cdot\mathrm{rem} + f a\log^4 b$, where $\mathrm{rem}$ is the total remainder. So $y$ has covolume at most $c = nL$, by `New.TwistedLattice.covolumeLe_of_normSqAt_le`.

Then Theorem C gives $d(\mathrm{mainAmount} - 3fa\log^4 b) \leq nL + 2\delta$. The main inequality compares the two sides. The terms $d\cdot\mathrm{mainAmount}$ and $n\cdot\mathrm{mainAmount}$ cancel up to errors, and what is left bounds $m\cdot\mathrm{rem}$.

### The chain of the proof

The proof has five steps. Each step names its section.

1. A twist for each prime (Section 4). A regular family $\theta$ of $m$-fold twists exists (Volume 12). For each $1 \leq j \leq m$ the height of one lift gives the bound $d(fa\log^4 b/m - k\cdot\mathrm{directionAmount})$ for the family $Z_j(1)/Z_j(\theta(\iota))$.
2. Auxiliary forms (Section 3). Some forms auxiliary for one scalar $\gamma$ span the target. So $y$ extends by $n'$ auxiliary forms $z$ to a basis, with $d = n + n'$.
3. The three bounds (Sections 3 and 4). The forms $z_i$ have $b_{\mathrm{short}} = 2x_1^2b^2$. The family $|\gamma(\theta(\iota))|^{-2}$ has height at most $b_{\mathrm{denom}} = b$. The family $Z(1)/Z(\theta(\iota))$ has height at most $b_{\mathrm{volume}} = d(b + fa\log^4 b - \mathrm{mainAmount})$.
4. The frame (Section 2). The theorem on a twist for each prime gives $0 \leq c + 2\delta + n'(2x_1^2b^2 + b) + d(b + fa\log^4 b - \mathrm{mainAmount})$.
5. The arithmetic (Sections 3 and 5). The completion costs $n'(2x_1^2b^2 + b) \leq d\,b$, and $b \leq fa\log^4 b$. So the right side is at most $c + 2\delta + 3dfa\log^4 b - d\cdot\mathrm{mainAmount}$.

### The results of the other chapters

The proof uses one result of each of these chapters. Section 6 gives the exact declarations.

- Chapter 2, [twists, critical pairs and regular families](/chapter/twists-critical-pairs/#regular-families-of-twists): the definitions of small ratios, denominator bounds and regular families, and the statement of their existence.
- Chapter 3, [single theta lifts](/chapter/single-theta-lifts/): the single lifts are injective, so $Z_j(\vartheta) > 0$.
- Chapter 4, [character lifts and tested forms](/chapter/character-lifts/): the norm of a character lift, used in the definition of the denominator bounds.
- Chapters 5 and 6, the exchange identity ([part 1](/chapter/exchange-identity-1/), [part 2](/chapter/exchange-identity-2/)): the exchange data that the squares and the gluing maps use.
- Chapter 7, [seesaw squares](/chapter/seesaw-squares/): the one square identity, which gives the commutation of the triangle of lifts.
- Chapter 8, [the chain determinant](/chapter/chain-determinant/#good-forms-and-the-factorization): the factorization of $Z(\vartheta)/Z(1)$ into the single lift determinants and a scalar of quotient ratios, and the height bound for the inverse of that scalar.
- Chapter 9, [the comparison operator, part 1](/chapter/comparison-operator-1/): the glued lattices and the first factors of the comparison operator.
- Chapter 10, [grids, columns and turns](/chapter/grids-paths-turns/): the turn ratios and their property of being ramified ratios.
- Chapter 11, [deep level Poincaré series](/chapter/deep-level-poincare/#denominators-sizes-and-spanning-forms): forms of principal level on $Y_0$ with integral and short lifts span.
- Chapters 12 to 15, [false lifts](/chapter/false-lifts/), [sharpness](/chapter/sharpness/), [the comparison operator, part 2](/chapter/comparison-operator-2/) and [Hecke values](/chapter/hecke-values/#heights-of-inverse-ratios): the five properties of the comparison operator, and the height of the inverse ratios of Hecke values.
- Chapter 16, [the height of one lift determinant](/chapter/lift-volume-height/#the-height-bound): the bound $d\,k(\log b\cdot\mathrm{denominatorBudget} - \mathrm{directionAmount})$ for $Z_j(1)/Z_j(\theta(\iota))$.

From other volumes the proof uses the twisted lattices and the target lattice of Volume 1, the good part of [the archimedean size](/chapter/archimedean-size/#the-good-part) of Volume 9, and the existence of regular families of Volume 12 ([regular families: the plan](/chapter/regular-families-plan/)).

### Background

The reader needs the heights of families indexed by $\iota$, and the product formula in the form of `New.HeightLe.neg_le_of_norm_map_le`: if a nonzero number $z$ has height at most $h$ as a constant family and $|\sigma z| \leq e^{h'}$ for all automorphisms $\sigma$ of $\mathbb{C}$, then $-h \leq h'$. The chapter [twisted lattices](/chapter/twisted-lattices/) proves this. The reader also needs the rules for heights: a product of families has height at most the sum of the heights (`New.HeightLe.mul`, `New.HeightLe.prod`), the $N$-th power has $N$ times the height (`New.HeightLe.pow`), and a height bound may be raised and the family made smaller at each $\iota$ (`New.HeightLe.mono`).

**Remark.** The source claims a proof of Theorem C, and Lean accepts the proof, if the reported checks hold. This chapter does not check the proof. It explains what the statements say and how they combine.
