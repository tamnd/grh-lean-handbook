---
title: What the chapter proves
lean:
  - New/Spanning/MainTerm/EnergyEstimate.lean
  - New/Spanning/RemainingTerms/Size.lean
  - New/Spanning/Unfolding/Climbing.lean
  - New/Spanning/Unfolding/Setup.lean
decls:
  - New.Filling.linkSecondMoment_isOpenElement_le
  - New.Filling.linkSecondMoment
  - New.Filling.fixer
  - New.Filling.IsOpenElement
  - New.Filling.mainSecondMoment
  - New.Filling.unipotentCovolume
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter belongs to layer 4 of [the four layers](/chapter/theorem-b-plan/#the-four-layers-of-the-proof) of the proof of Theorem B. It proves the bound for the main term of the second moment of the Poincaré map. The main term is the sum of the squared norms of the class sums over the open reductions. [The plan](/chapter/theorem-b-plan/) states the result as the theorem on the main term. This chapter states it again and proves it from the local densities of [the real places](/chapter/real-densities/) and [the finite places](/chapter/finite-densities/).

The chapter reads the sizes of [the data and its sizes](/chapter/data-and-sizes/). The letters are the letters of [the plan](/chapter/theorem-b-plan/). The field $E$ is a CM field with $f$ infinite places. The data $S$ is an admissible filling of shape $\mathfrak s$, with size parameter $b$, level $M = p_0 p_1$, a prime $N$, rank $k$ of $X_0$, depth $\varrho$ and $n = \varrho + 1$. For an infinite place $v$, $\Phi_v$ is the chosen complex embedding and $\kappa_v$ is the real number $M\,\Phi_v(\varpi)/(2\pi i)$.

### The main theorem

The sum on the left of the theorem is a sum in $[0, \infty]$. For a set $T$ of rational elements and a set $\Omega$ of reductions, it adds the squared norms of the blocks of the terms of $T$, one block for each pair of classes $c, c'$, each $s \in \Omega$ and each link $\Lambda$.

**Definition (Second moment by links).** For a set $T$ of rational elements of $G(E)$ and a set $\Omega$ of reductions,
$$\operatorname{linkSecondMoment}(T, \Omega) = \sum_{c, c'} \sum_{s \in \Omega} \sum_{\Lambda} \bigl\| A^{\mathrm{cut}}(T \cap \operatorname{link}^{-1}\{\Lambda\})(c, s, c') \bigr\|^2 \in [0, \infty],$$
where $A^{\mathrm{cut}}(T')(c, s, c')$ is the sum of the amplitudes of the cut Bessel function over the terms $\gamma \in T'$ over $(c, s, c')$, and $\Lambda$ runs over all $E$-submodules of $E^{\mathrm{Middle} \sqcup \mathrm{Middle}}$.

Lean: `New.Filling.linkSecondMoment` (New/Spanning/RemainingTerms/Size.lean).

The definition belongs to [the remaining terms](/chapter/remaining-terms/). It is stated here because the theorem uses it. The amplitude sums and the links are from [the anatomy of a term](/chapter/anatomy-of-a-term/) and [Poincaré series and unfolding](/chapter/poincare-series/).

Two conditions select the reductions. Let $S_g$ be a set of chosen places above $p_0$, and for each such place $w$ let $D_w$ be a nonzero vector of the span of the frame modulo $w$ or modulo its conjugate.

**Definition (Fixer and open elements).** The subgroup $\operatorname{fixer}(S_g, D)$ consists of the reductions $s$ that fix $D_w$ for every $w \in S_g$. A reduction $s$ is *open* if there is a chosen place $w$ above $p_0$ such that the leading principal minors of order $l < n$ of the matrix $(h(f_j, s f_l))_{j,l}$ are all nonzero. Here $f$ is the frame of $n$ vectors and $h$ is the form modulo $w$.

Lean: `New.Filling.fixer`, `New.Filling.IsOpenElement` (New/Spanning/Unfolding/Climbing.lean).

Both definitions belong to [Poincaré series and unfolding](/chapter/poincare-series/). The constants of the bound are the following. The main second moment is $\mathcal D_{\mathrm{main}} = d_S^2/(\deg \cdot \operatorname{mass})$, where $d_S$ is the dimension of the source, $\deg = \prod_v \deg_v$ is the product of the degrees of the Bessel systems, and $\operatorname{mass}$ is the mass of the genus of the standard Hermitian lattice of rank $r$. The number $\nu$ is the unipotent covolume of [the anatomy of a term](/chapter/anatomy-of-a-term/).

Lean: `New.Filling.mainSecondMoment`, `New.Filling.unipotentCovolume` (New/Spanning/Unfolding/Setup.lean).

**Theorem (The main term).** Let $S$ be admissible, let $S_g$ be a set of chosen places above $p_0$, and let $D$ be a choice of vectors as above. Then
$$\operatorname{linkSecondMoment}\bigl(\{\gamma : \operatorname{termDisc}\gamma \neq 0\},\ \{s \in \operatorname{fixer}(S_g, D) : s \text{ open}\}\bigr) \leq (1 + b^{-4})\,(b^{6k})^{-\# S_g}\, \mathcal D_{\mathrm{main}}\, \nu^2.$$
Here $\operatorname{termDisc}\gamma = |\Delta|^2 - N^2|\Delta'|^2$, with $\Delta$ the determinant and $\Delta'$ the leading minor of size $\varrho$ of the frame products of $\gamma$.

Lean: `New.Filling.linkSecondMoment_isOpenElement_le` (New/Spanning/MainTerm/EnergyEstimate.lean).

The right side is the real number on the right, sent to $[0, \infty]$ by `ENNReal.ofReal`. The proof is in [Section 9](/chapter/main-term/#the-energy-estimate). The other sections build the parts.

**Remark (Formalization).** The number $\nu$ is an explicit expression in $M$, $N$, $\operatorname{vol}\hat{\mathcal O}$, the discriminant of $E$ and the frame scales. It is the covolume of the integral unipotent group in the real unipotent group if $E$ contains a primitive $5040$-th root of unity (`New.Filling.lintegral_classCutoff_eq_unipotentCovolume`). The theorem itself does not ask for this root of unity. The constant $\mathcal D_{\mathrm{main}}$ is a quotient of reals. It is the textbook number if $\deg \cdot \operatorname{mass} \neq 0$; the degrees and the mass are positive, so no junk value $x/0 = 0$ enters.

### A model case

The heart of the chapter is a one-sided sieve. Its model is the large sieve in one variable. Let $a_1, \dots, a_m$ be complex numbers and $x_1, \dots, x_m$ real points with $|x_i - x_j| \geq \delta$ for $i \neq j$. Let $F \geq 0$ be a function on $\mathbb R$ whose Fourier transform $\hat F(\xi) = \int F(t) e(-\xi t)\,dt$ vanishes outside the open interval $(-\delta, \delta)$ and with $F \geq 1$ on $[0, 1]$. For $t \in [0, 1]$,
$$\Bigl|\sum_i a_i e(x_i t)\Bigr|^2 \leq \Bigl|\sum_i a_i e(x_i t)\Bigr|^2 F(t),$$
and the integral of the right side over $\mathbb R$ is $\sum_{i,j} a_i \bar a_j \hat F(x_j - x_i) = \hat F(0)\sum_i |a_i|^2$, because $\hat F(x_j - x_i) = 0$ for $i \neq j$. So the mean square of the sum is at most $\hat F(0) \sum |a_i|^2$. The bound is one-sided: it needs $F \geq 1$ on the range and $F \geq 0$ elsewhere, and nothing more.

The sieve of this chapter has the same shape. The points are lists of units of $E$, the frequencies are differences $\xi$ of inverses, and the function $F$ is a product of local forms. The term with $\xi = 0$ is the mass; it gives the main term. The terms with $\xi \neq 0$ are not $0$ but small: the decay $\beta(\xi)$ of the local forms bounds them. Poisson summation in $E$ turns the sum over the lattice points into the integral plus the sum over the dual frequencies.

### The sketch

The proof has six steps.

1. *Sieve systems.* A sieve system is a family of forms $J_0, \dots, J_{n}$ on pairs of lists, each the integral of the next over a common entry. A finite product of systems is a system. The sums of the forms over a finite family of lists with a common entry are nonnegative and lower semicontinuous. This is [Section 2](/chapter/main-term/#sieve-systems).
2. *Frequencies.* The sum of $\prod_v \max(1, |\nu|_v)^{-6}\, N(\operatorname{den}\nu)^{-3}$ over any finite set of $\nu \in E$ is at most $(64 \cdot 38\, e^4)^f$. This is [Section 3](/chapter/main-term/#frequencies-and-poisson-summation), with the one-sided Poisson summation.
3. *The global sieve.* For a sieve system at the infinite places and at a finite set $T$ of places, the sum of the top forms over lists of units of $E$ is at most the product of the constants of Poisson summation times the mass plus a small error. This is [Section 4](/chapter/main-term/#the-global-sieve).
4. *The place at $T$ and Kloosterman sums.* The finite places outside $T$ are absorbed. A class sum becomes a sum over double cosets of a Kloosterman sum, which is an orbital integral at $T$, times an orbital integral at the infinite places. This is [Section 5](/chapter/main-term/#the-place-at-t-and-filling-data) and [Section 6](/chapter/main-term/#kloosterman-sums-and-unfolding).
5. *Siegel's bound.* Siegel's formula bounds the squared norms of the class sums with one last entry by the densities at the last entry. This is [Section 7](/chapter/main-term/#siegels-bound).
6. *Fixed lines and the energy estimate.* The forms at $T$, normalised by the mass ratio, are a sieve system with the mass $(1 + b^{-6})(b^{6k})^{-\#S_g}$. The sieve and Siegel's bound together give the theorem. This is [Section 8](/chapter/main-term/#fixed-lines-and-the-finite-system) and [Section 9](/chapter/main-term/#the-energy-estimate).

[Section 10](/chapter/main-term/#exercises-and-notes) has the exercises and the notes.

### What the chapter uses

Each result from an earlier chapter is stated in one line where it is used.

- The data, its shape and the standing hypotheses, from [the data and its sizes](/chapter/data-and-sizes/) and [the anatomy of a term](/chapter/anatomy-of-a-term/).
- The local bounds at a real place, from [Bessel functions at a real place](/chapter/bessel-real-place/) and [local densities at the real places](/chapter/real-densities/).
- The lattice data, the Bessel vector, the forms of the floors, the decay and the mass integral at a finite place, from [local densities at the finite places](/chapter/finite-densities/).
- The amplitude sums, the links, the climbing groups and the fixers, from [Poincaré series and unfolding](/chapter/poincare-series/).
- The second moment by links, from [the remaining terms](/chapter/remaining-terms/).
- Siegel's formula with one vector, from [the chapter on the Siegel-Weil formula](/chapter/siegel-weil/), and the adeles and strong approximation, from [adeles and Hermitian spaces](/chapter/adeles-hermitian-spaces/).

The chapter uses no result of a later chapter. The files EnergyEstimate.lean and GlobalSieve.lean import files of [the remaining terms](/chapter/remaining-terms/) and [the anatomy of a term](/chapter/anatomy-of-a-term/); GlobalToLocal.lean, SiegelTopBound.lean and FixedLines.lean import files of [Poincaré series and unfolding](/chapter/poincare-series/). These chapters come before this one in the volume.
