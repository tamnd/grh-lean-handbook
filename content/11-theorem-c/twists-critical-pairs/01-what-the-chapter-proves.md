---
title: What the chapter proves
lean:
  - New/Determinant/Twist/FitTwists.lean
  - New/OneLift/HeckeValues/TwistedRatio.lean
  - New/Determinant/Twist/LongForms.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

Theorem C bounds the covolume of the lattice of target forms from below. [Theorem C and the height argument](/chapter/theorem-c-plan/) explains the method: the covolume is compared at the trivial twist and at a twist $\vartheta$, and the quotient is a nonzero algebraic number. A nonzero algebraic number cannot be small at every place. So a bound for its height gives a lower bound for the covolume. This chapter supplies the objects that the comparison is made with: the twists, the critical pairs and their ratios of Hecke values, and the regular families of twists. It proves the facts about these objects that the later chapters of the volume use, and it states the existence of regular families, which Volume 12 proves.

### Where the chapter sits

The proof of Theorem C has four inputs ([the four inputs](/chapter/theorem-c-plan/#the-four-inputs)). Two of them speak of ratios of $L$-values. The factorization of the chain determinant has a scalar factor that is a product of ratios of Hecke values at the powers $\vartheta^{j-i}$ ([the chain determinant and its factorization](/chapter/chain-determinant/)). The height of one lift determinant has a factor that is a power of the inverse of a ratio of Hecke values ([the height of one lift determinant](/chapter/lift-volume-height/)). Both factors must have controlled height, and the twist must be chosen so that they do. A regular family is a choice of one twist for each prime $\ell$ and each isomorphism $\iota : \mathbb{C} \to \overline{\mathbb{Q}}_\ell$ that has this control. The proof of Theorem C takes one regular family at the start and uses it to the end ([the proof of Theorem C](/chapter/proof-of-theorem-c/)).

So the chapter has two halves. The first half (Sections 2 to 5) is about one twist at a time. It defines the twists and the critical pairs, proves that the ratio of a pair is a nonzero real number, writes the ratio as a quotient of two positive squared norms of theta lifts, and factors a product of $L$-values of a twisted character into the untwisted product, a power of $\mathrm{Nm}\,Q$ and squared ratios. The second half (Section 6) is about families. It defines what it means that a family of twists has small ratios and small denominators, and it states the theorem that such a family exists.

### A model case

The phenomenon behind the ratios is classical. Let $\chi_5$ be the quadratic character modulo $5$, so $\chi_5(n) = (n/5)$. It is even, since $\chi_5(-1) = 1$. Euler computed $\zeta(2) = \pi^2/6$, and the generalized Bernoulli numbers give

$$L(2, \chi_5) = \frac{4\pi^2}{25\sqrt 5}.$$

A numerical check: the partial sums $1 - \tfrac14 - \tfrac19 + \tfrac1{16} + \tfrac1{36} - \tfrac1{49} - \cdots$ approach $0.7062$, and $4\pi^2/(25\sqrt5) = 0.70621\ldots$. Each value is a power of $\pi$ times an algebraic number, and the power of $\pi$ is the same, because both characters are even and the point $s = 2$ is the same. So the ratio

$$\frac{L(2, \chi_5)}{\zeta(2)} = \frac{24}{25\sqrt 5}$$

is algebraic. The transcendental period cancels. Three features of this example come back in the source.

1. The ratio has a denominator at the conductor $5$. In the source the denominator at the places of the modulus $Q$ of the twist is a power of $\mathrm{Nm}\,Q$, and it is harmless at every prime $\ell$ prime to $\mathrm{Nm}\,Q$. Section 5 proves this in the form that the source uses: a bound for a height survives multiplication by powers of $\mathrm{Nm}\,Q$.
2. The inverse ratio $25\sqrt5/24$ has denominators at $2$ and $3$, the primes that divide the numerator $24$. These are congruence primes: at such a prime the twisted value is divisible, and the inverse ratio is large in the $\ell$-adic sense. Small ratios, in the sense of Section 6, bound these denominators over all primes at once.
3. Each $L$-value is a period times an algebraic number, and the period is the same for the twisted and the untwisted value. In the source the role of the period is played by a constant $A \neq 0$ that does not depend on the twist, and the algebraic number is the squared norm of a theta lift of the character to a definite unitary group (Section 4). The constant cancels in the ratio.

The source never uses the closed formula for $L(2, \chi_5)$, and it does not prove the algebraicity of Hecke values in general. It needs only the three features above, and it proves each in the form it uses.

### The objects in one paragraph

Let $E$ be the CM field of the data, $S$ the set of chosen places, and $m$ the number of lifts. A *tame character* $\vartheta$ is a character of $U(1)(\mathbb{A}_E)$ of weight $0$ with tame ramification at a finite set $Q$ of places. A *twist* is ramified at every place of $Q$, and an *$m$-fold twist* has its first $m$ powers ramified there. A *critical pair* $p = (\nu, z)$ is a character $\nu$ of weight $-c$ with $z \leq c \leq 4b$ and tame part on $S$, with a point $1 \leq z \leq t$. Its *ratio* at $\vartheta$ is $|L^{S \cup Q}(z, (\nu\vartheta)^{-1})|/|L^S(z, \nu^{-1})|$. A family $\theta$ of $m$-fold twists, one for each $\iota$, is *regular* if the moduli are prime to the primes of the $\iota$, the inverse ratios have height at most $x_1$, and the denominators of the projections to the spaces of lifts add up, over all primes, to at most $\mathrm{denominatorBudget} = f a \log^3 b/(mk)$.

### What the chapter uses

The chapter uses four results of earlier volumes and one forward result. From Volume 1: the characters, twists and $m$-fold twists of [fields, places and twists](/chapter/fields-places-twists/), the sizes of [the data and its sizes](/chapter/data-and-sizes/), and the heights of [twisted lattices](/chapter/twisted-lattices/). From Volume 6: the products $L_*$ of $L$-values of [the Rallis inner product formula](/chapter/rallis-inner-product/). From Volume 11, chapter 10: the squared norm of the theta lift of a character as an $L$-value, which [Hecke values of character lifts](/chapter/hecke-values/) proves. Section 4 states that result in full. The existence of regular families is proved in Volume 12, and Section 6 states it in full.

### A sketch of the proofs

Most results of the chapter are short, and their proofs are complete here. There are three ideas.

The first idea is non-vanishing. The $L$-function of $\nu$ is the $L$-function of the Hecke character $x \mapsto \nu(x/\bar x)$ of $E$. If $\nu$ has a nonzero weight, this Hecke character is not trivial, and its $L$-function does not vanish at real $s \geq 1$. A critical pair has weight $-c$ with $c \geq z \geq 1$, and a tame character has weight $0$. So both $L$-values in the ratio are nonzero, and the ratio is not $0$ (Section 3).

The second idea is the inner product formula. The squared norm of the theta lift of $\nu\vartheta$ from $U(1)$ to the definite group $U(2z)$ is $C \cdot L^{S \cup Q}(z, (\nu\vartheta)^{-1}) \cdot \mathrm{Nm}\,Q^{2z - 1}$, with a constant $C \neq 0$ that does not depend on $\vartheta$. Divide by $\mathrm{Nm}\,Q^{2z-1}$ and by the same number at $\vartheta = 1$. The constant cancels, and the ratio is a quotient of two positive numbers (Section 4).

The third idea is bookkeeping with Euler factors. The product $L_*$ of squared $L$-values up to $z$ at a twist is the untwisted product times $\mathrm{Nm}\,Q^{z^2}$ times the squared ratios at the points $1, \dots, z$. Powers of $\mathrm{Nm}\,Q$ do not change the height of a family when $\mathrm{Nm}\,Q$ is prime to $\ell$ (Section 5).

**Remark (Formalization).** The two files of the chapter have different roles. `New/Determinant/Twist/FitTwists.lean` is a file of definitions. Its only theorems are three equations for the trivial twist, their conjunction, and the lemma that main pairs are ramified. `New/OneLift/HeckeValues/TwistedRatio.lean` proves the results of Sections 3 to 5. The definitions of FitTwists are used by the proof of Theorem C and by the whole of Volume 12, which imports the file.
