---
title: How the three theorems fit together
lean:
  - New/Reduction/MainInequality.lean
  - New/Reduction/Lattices/TwistedLattice.lean
decls:
  - New.TwistedLattice.covolumeLe_of_normSqAt_le
  - New.Data.mainAmount_nonneg
status: drafted
drafted_by: writer@claude-opus-5-5
---
## How the three theorems fit together

This section shows how [the main inequality](/chapter/main-inequality/) uses Theorems A, B and C, which terms cancel, and where the argument needs a number to be nonzero. The main inequality is `New.star_inequality`: for the data $D$, $m\cdot\mathrm{rem} \leq f a\log^5 b$. The next chapter proves it in full. The three theorems contain all the analysis and the arithmetic, and the rest is bookkeeping.

### The assembly

Write $\mathrm{loss} = f a\log^4 b$, $\mathrm{err}_0 = f a\log^3 b$ and $\mathrm{indexPerDim} = 10\log(1 + 2b^2)\cdot\mathrm{err}_0$.

1. *Few translates.* Theorem B gives $d_T > 0$ and a set $\mathcal{T} \subseteq \bar G$ with $\#\mathcal{T}\cdot\dim\mathrm{src} \leq 5d_T\log(1 + 2b^2)$, whose images span at least $(1 - 4/b^2)d_T$ dimensions.
2. *Short forms.* Let $\mathrm{short}$ be the set of integral source forms $\varphi$ with $\|\Theta_1(s\mathfrak{p}\varphi)\|_\sigma^2 \leq \exp(\mathrm{main} - m\,\mathrm{rem} + \mathrm{loss})$ for all $s$ and $\sigma$. Theorem A (a) says that $\mathrm{short}$ spans $\mathrm{src}$.
3. *The family.* Choose a basis $y_1, \dots, y_n$ of the span of the vectors $s\mathfrak{p}\varphi$, $s \in \mathcal{T}$, $\varphi \in \mathrm{short}$, among these vectors. By step 2 this span is that of step 1, so $(1 - 4/b^2)d_T \leq n \leq d_T$.
4. *Covolume.* Each $y_i$ has squared norm at most $\exp(\mathrm{main} - m\,\mathrm{rem} + \mathrm{loss})$ at every $\sigma$. Hadamard's inequality gives covolume at most $n(\mathrm{main} - m\,\mathrm{rem} + \mathrm{loss})$.
5. *Index.* Theorem A (b) gives index at most $\#\mathcal{T}\cdot\dim\mathrm{src}\cdot 2\,\mathrm{err}_0$, and step 1 bounds this by $d_T\cdot\mathrm{indexPerDim}$.
6. *Comparison.* Theorem C gives $d_T(\mathrm{main} - 3\,\mathrm{loss}) \leq n(\mathrm{main} - m\,\mathrm{rem} + \mathrm{loss}) + 2d_T\,\mathrm{indexPerDim}$.
7. *Cancellation.* As $\mathrm{main} + \mathrm{loss} \geq 0$ and $n \leq d_T$, we have $n(\mathrm{main} + \mathrm{loss}) \leq d_T(\mathrm{main} + \mathrm{loss})$. With step 6 this gives $n\cdot m\,\mathrm{rem} \leq d_T\cdot\mathrm{err}$, with $\mathrm{err} = 4\,\mathrm{loss} + 2\,\mathrm{indexPerDim}$.
8. *Division.* As $4/b^2 \leq 1/2$, step 3 gives $d_T \leq 2n$, so $n > 0$ and $m\,\mathrm{rem} \leq 2\,\mathrm{err}$. The sizes give $|2\,\mathrm{err}| \leq f a\log^5 b$.

**Theorem (Hadamard's bound for the covolume).** Let $\mathcal{L}$ be a twisted lattice and let $z_1, \dots, z_n$ be vectors with $\|\Theta_1 z_i\|_\sigma^2 \leq e^h$ for all $i$ and all $\sigma$. Then $z$ has covolume at most $nh$.

Lean: `New.TwistedLattice.covolumeLe_of_normSqAt_le` (New/Reduction/Lattices/TwistedLattice.lean).

**Lemma (The sign of the main amount).** $\mathrm{main} \geq 0$.

Lean: `New.Data.mainAmount_nonneg` (New/Reduction/PrimeSums.lean).

Step 7 is the only place where the sign of the main amount matters. In step 6 the left side has the factor $d_T$ and the right side has the factor $n$, and the difference $(d_T - n)\,\mathrm{main}$ is not small. Since $\mathrm{main} + \mathrm{loss} \geq 0$ and $n \leq d_T$, this difference is on the correct side, and it drops out. The share $4/b^2$ of Theorem B is used in two other places: Theorem C needs it to bound the cost of completion by $d_T b$, and step 8 uses $n \geq d_T/2$.

### What cancels

The final inequality is a bound for a remainder of prime sums, and the main terms cancel in several places.

1. The main amount, between the upper bound of Theorem A and the lower bound of Theorem C, in step 7.
2. The gains $\sum_\ell \mathrm{gain}_\ell\log\ell$ in the size of the chain, against $\log c_B$, inside Theorem A (a) (Section 3).
3. The constant $c_1$, the real part of a mean of logarithmic derivatives, between the period and the expected value $a(\log(a/\bar\kappa) + c_1)$ of the prime sums (`New.Data.jetSize_sub_mainPrimeSum_le`).
4. The excesses $a\log(\bar\kappa M\,\mathrm{rd}_E/2\pi)$ of the $m$ lifts, against $a\log N$, up to $O(a\log b)$, where $\bar\kappa$ is the geometric mean of the weights and $\mathrm{rd}_E$ the root discriminant of $E$ (`New.Data.mul_jetSize_sub_mainPrimeSum_sub_le`).
5. The main terms of the prime sums against their expected value, which leaves the total remainder as a combination of the remainders $R_{q_0}(x) - R_{q_0}(x_1)$ and $R_1(x_1)$ (`New.Data.totalRemainder_eq`).
6. A constant that depends on $q_0$, between the two cut-offs (`New.Data.sum_aPlaces_primeSum`).

Items 1 and 2 are in this chapter. Items 3 to 6 are in [the prime sums](/chapter/prime-sums/) and in Volume 9.

### Where the nonvanishing comes from

The argument is a comparison of a nonzero algebraic number with its conjugates. It needs that number to be nonzero, and it needs the normalizing constants to be nonzero. The seesaw constant $c_{ss}$ of Section 2 is a unit by its type, but the identity that defines it carries no information if $c_0 C/d = 0$. The nonvanishing that the argument uses comes from other places.

1. *The Gram determinant.* In the proof of a twist for each prime, $\operatorname{Gram}(1) \neq 0$ because $(y, z)$ is a basis and $\Theta_1$ is injective. The injectivity is `New.Data.injective_lift_targetLattice`: the lower chain at the level is injective.
2. *The volume.* $Z(\xi) \neq 0$ for every twist, by `New.TwistedLattice.volume_ne_zero`, from the same injectivity.
3. *The squares of the chain.* The scalars of a commuting chain in a triangle of lifts do not vanish (`New.Exchange.IsTriangle.ne_zero_of_chainCommutes`), which the factorization of the chain determinant uses.
4. *The Hecke values.* The ratios of Hecke $L$-values are nonzero (`New.Data.CriticalPair.ratio_ne_zero`), as the characters have nonzero weight. So the numbers $\gamma(\vartheta)$ and the turn ratios are nonzero.
5. *The scalars of $\mathfrak{p}$.* The gain factor is positive (`New.Data.invGainFactor_pos`), so $\mathfrak{p}$ and the good Poincaré maps have the same ranges.

**Remark (Formalization).** Section 2 shows that if $c_0 C/d = 0$, the source sets the normalizing unit to $1$, and the seesaw identity then carries no information. The statements of Theorem A are upper bounds for the size and the index of the images of $\mathfrak{p}$, and they are proved for the constant that the source chooses, whatever it is. The lower bound of Theorem C does not use $c_{ss}$. It uses only the nonvanishing in items 1 to 4. So no step of the main inequality divides by $c_0 C/d$.
