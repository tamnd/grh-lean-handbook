---
title: What the chapter proves
lean:
  - New/Reduction/ShortAndEnough.lean
  - New/Reduction/MainInequality.lean
decls:
  - New.Data.integralRamified
  - New.Data.span_short_integralRamified_eq_top
  - New.Data.indexLe_normalizedPoincare
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter is the last chapter of the volume. It assembles Theorem A from the results of chapters 2 to 14 and from a few results of Volumes 1 and 10. It states Theorem A as Lean states it, and it gives the whole proof. Each input is stated exactly as the source proves it, with a link to the section that proves it. The chapter tracks every constant. Section 8 maps the proof to the declarations of the source, and Section 9 compares the plan of the volume with the source.

[Theorem A and its plan](/chapter/theorem-a-plan/) gives the motivation, a model case and a short form of the proof. This chapter does not repeat the motivation. It proves in full the steps that the plan only names, in particular the passage from the composite lift to the target. All the steps are in one file, New/Reduction/ShortAndEnough.lean, in its first part. The second part of the file proves Theorem B, and [the proof of Theorem B](/chapter/proof-of-theorem-b/) explains it. The chapter [Theorems A, B and C](/chapter/theorems-a-b-c/#theorem-a-short-forms-of-small-index) of Volume 1 gives a short form of the same proof.

### The notation

Fix parameters $P$ and admissible data $D$ for $P$. The letters are those of [the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes).

1. $x$, $x_1$ and $b$ are the three scales, with $x^{10^6} \leq x_1$ and $x_1^{10^6} \leq b$. The number $\log b$ is `D.logB`. The long order is $a = xb$.
2. $m$ is the number of lifts, $k$ is the rank of the source space $X_0$, and $f$ is the number of infinite places of the CM field $E$.
3. $N$ is the prime level, and $K = \mathbb{Q}(\sqrt{-d})$. The set $\mathcal{S}$ is the set of primes $p < x_1$ with $\chi_K(p) \neq 1$, the small nonsplit primes.
4. $\mathrm{err}_0 = \mathrm{errorUnit} = f a \log^3 b$ is the unit of loss.
5. $D_X$ is the dimension over $\mathbb{C}$ of the space of all source forms. The source $\mathrm{src}$ is the subspace of ramified source forms. The target $T$ is the space of target forms, the good forms on the space $Y_0$.
6. $\bar G$ is the finite group `D.chosenGL`, and $e_0$ is the central idempotent of $\mathbb{C}[\bar G]$ that cuts out the good part.
7. $\mathcal{P}$ is the Poincaré map from source forms to forms on $Y_0$, without the factor `poincareScale`.
8. $\Theta_\vartheta$ is the chain of $m$ lifts of target forms for the $m$-fold twist $\vartheta$, and $\Theta_1$ is the chain for the trivial twist. For an automorphism $\sigma$ of $\mathbb{C}$, $\|\Theta_1 y\|_\sigma^2$ is the class sum of the squared Weyl norms of the values of the $\sigma$-conjugate of $\Theta_1 y$.
9. $\iota$ runs over the pairs of a prime $\ell$ and a ring isomorphism $\mathbb{C} \cong \overline{\mathbb{Q}}_\ell$ (`New.PrimePadicIso`). Each $\iota$ gives an embedding $\mathbb{C} \to \mathbb{C}_\ell$, the place of $\iota$.
10. $\mathrm{mainAmount}$ and $\mathrm{rem} = \mathrm{totalRemainder}$ are the numbers of [the prime sums](/chapter/prime-sums/#jet-sizes-the-direction-amount-and-the-main-amount).

The normalized map $s\mathfrak{p}$, for $s \in \bar G$, is $s\mathfrak{p}\,\varphi = c_B\cdot\#\bar G\cdot e_0\,s\,\mathcal{P}(c_{ss}^{-1}\varphi)$. Here $c_B$ is the gain factor and $c_{ss}$ is the seesaw constant. Section 5 defines both and the map.

### The statement

**Definition (Integral ramified forms).** The set $\mathrm{src}_{\mathrm{int}}$ is the set of ramified source forms $\varphi$ such that for every $\iota$ the form $\varphi$ lies in the integral source forms at the place of $\iota$: every value $\varphi(g)$ has gauge at most $1$ for the Weyl lattice at $g$.

Lean: `New.Data.integralRamified` (New/Reduction/ShortAndEnough.lean).

The set $\mathrm{src}_{\mathrm{int}}$ is not a complex subspace. At each $\iota$ the integral forms are a module over the ring $\mathcal{O}_\iota$ of complex numbers $z$ with $|\iota z| \leq 1$.

**Theorem (Theorem A (a), short forms).** The span over $\mathbb{C}$ of the set of $\varphi \in \mathrm{src}_{\mathrm{int}}$ such that

$$\|\Theta_1(s\mathfrak{p}\,\varphi)\|_\sigma^2 \leq \exp\bigl(\mathrm{mainAmount} - m\cdot\mathrm{rem} + f a\log^4 b\bigr)$$

for every $s \in \bar G$ and every automorphism $\sigma$ of $\mathbb{C}$ is all of $\mathrm{src}$.

Lean: `New.Data.span_short_integralRamified_eq_top` (New/Reduction/ShortAndEnough.lean).

**Theorem (Theorem A (b), small index).** Let $t$ be a finite subset of $\bar G$, and let $y_1, \dots, y_n$ be target forms such that for each $i$ there are $s \in t$ and $\varphi \in \mathrm{src}_{\mathrm{int}}$ with $y_i = s\mathfrak{p}\,\varphi$. Then the family $y$ has index at most

$$\#t\cdot\dim_{\mathbb{C}}\mathrm{src}\cdot 2 f a\log^3 b$$

in the target lattice.

Lean: `New.Data.indexLe_normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

Section 6 proves part (a), and Section 7 proves part (b). The index is the notion of Section 3.

### Where Theorem A is used

The main inequality $m\cdot\mathrm{rem} \leq f a\log^5 b$ is `New.star_inequality` at [line 87](lean:New/Reduction/MainInequality.lean#L87). Its proof, in [the main inequality](/chapter/main-inequality/#the-main-inequality), uses both parts. Part (a) gives a spanning set of short integral forms. Theorem B chooses a set $t$ of translates with $\#t\cdot\dim\mathrm{src} \leq 5\,d_T\log(1 + 2b^2)$, where $d_T = \dim T$, and finds a large independent family among the images. Part (b) then bounds the index of this family by $5\,d_T\log(1 + 2b^2)\cdot 2 f a\log^3 b$. Theorem C bounds the same family from below. So the three numbers of Theorem A that matter downstream are the exponent $\mathrm{mainAmount} - m\cdot\mathrm{rem} + f a\log^4 b$, the factor $\#t$, and the loss $2 f a\log^3 b$ per dimension.

### What the chapter uses

The proof has three inputs from this volume and a frame from Volume 1.

1. The divisibility of the composite lift prime by prime, from [divisibility prime by prime](/chapter/divisibility/).
2. The seesaw identity, from [the seesaw identity, part 2](/chapter/seesaw-identity-2/).
3. The archimedean size of the composite lift and two lemmas on the good part, from [the archimedean size](/chapter/archimedean-size/).
4. The spanning by short ramified forms, the gain and the dimension of the source, from [short columns and the gain](/chapter/short-columns-gain/).
5. The colength, the index and the target lattice, from [colength](/chapter/twisted-lattices/#colength), [twisted lattices, index and covolume](/chapter/twisted-lattices/#twisted-lattices-index-and-covolume) and [the target lattice](/chapter/integral-target-forms/#the-target-lattice).

The Poincaré map and the map $\#\bar G\,e_0\,s$ are defined in files of Volume 10, which ShortAndEnough.lean imports. [The objects of the upper bound](/chapter/upper-bound-objects/) describes the Poincaré map as a Bessel period. Sections 2 and 3 state every input.

### A sketch of the proof

For part (a), take a short ramified form $\varphi$: integral at every $\iota$, with all conjugates of all values of squared norm at most $e^{\mathrm{err}_0}$. Such forms span $\mathrm{src}$. Put $z = \mathcal{P}(c_{ss}^{-1}\varphi)$. The seesaw identity gives $\iota_1 z = B_{1,\Psi}\varphi$ for a chain datum $\Psi$. The size theorem bounds the values of $\sigma B_{1,\Psi}\varphi$ by $\exp(\mathrm{err}_0 + \beta)$, where $\beta$ contains the term $2\sum_{p\in\mathcal{S}}\mathrm{gain}_p\log p$. The passage to the good part adds $x^{99}$. The factor $c_B$ multiplies the squared norm by $c_B^2$, and $2\log c_B$ removes the term with the gains, at the cost of $2\mathrm{err}_0 + 2b$. The sizes of the data absorb all errors into $f a\log^4 b$.

For part (b), fix $\iota$ above $\ell$. The divisibility gives a submodule $S$ of colength dividing $\ell^j$, with $j \leq \mathrm{err}(\ell)D_X$, on which every composite lift prime to $\ell$ is divisible by $\ell^{\mathrm{gain}_\ell - \mathrm{err}(\ell)}$. The factor $c_B$ has $\iota$-adic absolute value $|\ell^{-g_\ell}|$, with $g_\ell = \lfloor\mathrm{gain}_\ell - \mathrm{err}(\ell)\rfloor$, so $s\mathfrak{p}$ maps $S$ to integral target forms. The colength gives an index with $e(\ell) = D_X\,\mathrm{err}(\ell)$. As $D_X \leq 2\dim\mathrm{src}$ and $\sum\mathrm{err}(\ell)\log\ell \leq \mathrm{err}_0$, one translate costs $\dim\mathrm{src}\cdot 2\mathrm{err}_0$. The translates add.

### The plan of the chapter

Section 2 states the inputs from this volume. Section 3 states the colength, the index and the target lattice. Section 4 defines the divisibility errors and the gain factor and bounds them. Section 5 defines the normalized map and proves its three properties. Section 6 proves part (a), and Section 7 proves part (b). Section 8 gives the map of the proof, and Section 9 checks the plan. Section 10 has exercises and notes.
