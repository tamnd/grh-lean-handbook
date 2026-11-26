---
title: What the chapter proves
lean:
  - New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean
  - New/Determinant/AuxiliaryForms/DeepLevelVanishing.lean
  - New/Determinant/AuxiliaryForms/FirstPath.lean
  - New/Determinant/AuxiliaryForms/SpanningForms.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

Theorem C is a lower bound for the covolume of the integral target forms ([the plan of the main theorem](/chapter/theorem-and-plan/)). [The plan of Theorem C](/chapter/theorem-c-plan/) splits its proof into four inputs. The first input is the theorem on auxiliary forms ([the four inputs](/chapter/theorem-c-plan/#the-four-inputs)). It asks for many forms $y$ on $Y_0$ whose chains of lifts $\iota_\vartheta y$ are integral at the primes prime to $\mathrm{Nm}\,Q$, after a scalar $\gamma(\vartheta)$, and are small for the trivial twist. This chapter proves the part of Input 1 that lives on the full space of forms on $Y_0$. The passage to the target forms is in `New.Determinant.Twist.LongForms` ([Theorems A, B and C](/chapter/theorems-a-b-c/)).

The main result of the chapter is the theorem on spanning forms ([exists_span_short_lifts_eq_top](/decl/New.Data.exists_span_short_lifts_eq_top/), Section 8). In words: there are constants $c(\vartheta) \neq 0$, one for each $m$-fold twist, with $|c(\vartheta)|$ equal to the product of the turn ratios up to a constant and a power of $\mathrm{Nm}\,Q$, such that the space of forms of principal level on $Y_0$ is spanned by forms $y$ with two properties.

1. For every twist $\vartheta$ and every prime $l$ prime to $\mathrm{Nm}\,Q(\vartheta)$, the form $(c(\vartheta)/c(1))\,\iota_\vartheta y$ is integral at $l$.
2. Every conjugate of every value of $\iota_1 y$ has squared Weyl norm at most $\exp(x^{202} b^2)$.

Here $x$ and $b$ are the length of the prime sum and the weight at the $b$-places ([the data and their sizes](/chapter/data-and-sizes/)).

### What the chapter uses

The chapter uses the following results. Each is stated where it is used, in one line with a link.

- Grids $Y$ and $\tilde Y$, grid paths, path data and their periods, from [seesaw squares and grid paths](/chapter/seesaw-squares/#grid-paths-and-turns).
- The triangle of lifts and the injectivity of its chains, from [the chain determinant](/chapter/chain-determinant/).
- The first columns of the grid, the turns, the diagonal turns and the last path, from [grids, columns and turns](/chapter/grids-paths-turns/). This chapter is being written now. We link to it by chapter.
- The first factors of the comparison operator, from [the comparison operator, part 1](/chapter/comparison-operator-1/). This chapter is also being written now.
- Steep parameters and the restriction theorem for matrix coefficients, from [Laplace's method](/chapter/laplace-method/).
- Cusp estimates, delta forms, gauges and the isomorphism between algebraic forms and forms of fixed level, from [automorphic forms](/chapter/automorphic-forms/).
- Integrality of theta kernels at primes prime to the modulus, from [theta kernels and gauges](/chapter/theta-kernels-gauges/).

No file of this chapter imports a file of a later chapter of this volume.

### The sketch

The argument has four steps. Each step is one file of the source.

**Step 1. Periods of Poincaré series of deep level (Sections 2 to 4).** Let $V$ be a hermitian space and $V \oplus \langle 1\rangle$ the space with one more basis vector $\tilde e$. A Poincaré series on $V \oplus \langle 1 \rangle$ sums the translates of a kernel over the rational points. Its period over $V$ is an integral over $V$ of the series times a form $F$ on $V$. Unfolding writes the period as a sum over the cosets of the rational points of $V$. A coset is fixed by its last column $\gamma\tilde e$. At deep level, the last columns that meet the level condition are far apart. The term of the identity coset is a convolution of $F$. A packing bound shows that the other terms are small. Section 2 also shows that the parameters of $Y_0$ and $\tilde Y^0_0$ are steep. This is the hypothesis of the restriction theorem at the real places.

**Step 2. A vanishing criterion (Section 5).** Let $y$ be a form on $V$ that is orthogonal to the restrictions of all forms of deep level on $V \oplus \langle 1 \rangle$. Then $y = 0$. The proof halves every bound $S$ of $\|y\|$. In the cusp, cuspidality gives the halving. Away from the cusp, the Poincaré series is a form of deep level, so its period against $y$ is $0$. Step 1 then makes the convolution of $y$ small, and a lower bound for the local pairing makes $y$ itself small.

**Step 3. The first path (Sections 6 and 7).** Apply Step 2 to $V = Y_0$ and $V \oplus \langle 1\rangle = \tilde Y^0_0$. The forms of deep level $\mathfrak b$ on $\tilde Y^0_0$ detect every form on $Y_0$. The transposed chain $\Theta^\flat$ maps the forms on the first row onto the forms of level $\mathfrak b$. Together these give a restriction map $\mathrm{res}^\flat$ from the forms of level $\mathfrak b$ onto the forms on $Y_0$. Its pairing with the chain of lifts is a period on the first path of the grid.

**Step 4. Spanning forms (Section 8).** The turns of [grids, columns and turns](/chapter/grids-paths-turns/) move a period from the first path to the last path. Each turn costs a turn ratio. On the last path the period $\Xi$ has small denominators and small conjugates. Delta forms read the values of the chain of lifts from such periods. The forms of level $\mathfrak b$ with short algebraic values span, and $\mathrm{res}^\flat$ is onto. So their images span the forms on $Y_0$, and they have the two properties.

### The model case

Let $V$ have rank $0$. Then $V \oplus \langle 1 \rangle$ is a line, and a form on it is a function on a finite set of classes. The period over $V$ is the value at the base point. A form of deep level that vanishes away from the base class exists, so a function on $V$ (a number) orthogonal to all such values is $0$. Step 2 is the version of this fact for a space of positive rank. The cosets of Step 1 replace the classes, and the packing bound replaces the finite count.

### Reading the chapter

Section 2 proves the steepness of the parameters. Volume 10 uses this result in [the Bessel functions at a real place](/chapter/bessel-real-place/). Sections 3 and 4 prove Step 1. Section 5 proves Step 2. Section 6 applies it to the grid. Section 7 builds the restriction map on the first path. Section 8 proves the spanning theorem. Section 9 has exercises and notes.

All statements are those of the source at the pin 72fead1. The source claims them, and Lean accepts them, if the reported checks hold.
