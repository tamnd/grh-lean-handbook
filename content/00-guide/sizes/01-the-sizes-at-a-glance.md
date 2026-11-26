---
title: The sizes at a glance
lean:
  - New/Reduction/Data/AdmissibleData.lean
  - New/Reduction/Data/Sizes.lean
  - New/Reduction/Data/Magnitudes.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The sizes at a glance

This chapter is a reference. It lists every scale and every parameter of the argument of the source, with its size as Lean states it, the declaration that states it, and the place where the argument uses it. It then explains the order of the scales and why each gap between two scales is as large as it is. The definitions and the proofs of the basic sizes are in [the data and its sizes](/chapter/data-and-sizes/) of Volume 1. This chapter does not repeat them. It collects them in one place, adds the file and the line of each, and adds the size conditions that later parts of the argument impose.

### Why a table of sizes

The argument of the source is quantitative from the first step to the last. It compares two bounds for the covolume of a lattice of automorphic forms. Each bound is a sum of a main amount and of error terms, and the main amounts cancel. So the proof needs, at each step, that one error term is small against another quantity. The source proves these comparisons with explicit numbers: the number $m$ of lifts lies in $[\sqrt{x}, 2\sqrt{x}]$, the rank $r$ lies in $[x^5, 3x^5]$, the primes $p_0$, $p_1$ lie in $[b^{10}, b^{11}]$, and so on. A reader who checks one step must know all of these numbers at once. The plan of the handbook asks for one table with one row for each constant, and this chapter is that table.

### The order of the scales

The data of the argument have three integer scales $x \leq x_1 \leq b$ and a fixed pair of parameters $P = (q_0, d)$. Here $q_0$ is a multiple of $18480$ and $d$ is a prime. Write $C_P$ for the constant of the parameters (`New.Parameters.constantBound`), a number that depends on $q_0$ and $d$ only. On the logarithmic scale the order is

$$C_P \ll \log\log b \leq \tfrac{1}{100}\log x \ll \log x \leq 10^{-6}\log x_1 \ll \log x_1 \leq (\log b)^{1/6} \ll \log b.$$

Each sign $\ll$ is one of five inequalities, the scale inequalities (S1) to (S5) of Section 2. The other quantities have a size in terms of these scales. The ranks have a degree in $x$: $m$ has degree $\tfrac12$, the ranks $r$, $k$ and the step $t$ have degree $5$, the number $f$ of infinite places of the CM field has degree $11$, and the gap $\Delta$ has degree $40$. The weights lie between $a/x_1$ and $b$, where $a = xb$. The primes of the level are powers of $b$: $p_0, p_1 \in [b^{10}, b^{11}]$ and $M = p_0 p_1 \in [b^{20}, b^{22}]$. The prime $N$ has $\log N \in [m \log b, 30 m \log b]$.

In the data that the source builds at the end of the proof, the sizes are much more extreme than the five inequalities say. There $0 < \varepsilon < 1/100$ is fixed, $x$ is a large integer, $x_1 = \lfloor \exp(x^{\varepsilon/6}) \rfloor$ and $\log b \in [x^\varepsilon, x^\varepsilon + 1]$. So $\log x_1$ and $\log b$ are powers of $x$, not multiples of $\log x$. Section 4 gives this construction.

### A picture in words

Think of a ruler that measures $\log\log$ of each quantity. Near the origin sit the constants of the parameters, $q_0$, $d$, $\varphi(q_0)$ and $C_P$. Far to the right sits $\log\log b$, at distance at least $10^{12} C_P$. The numbers $\log x$ and $\log x_1$ sit close to $\log\log b$ on this ruler, since $\log\log x \leq \log\log b$ and $\log\log x_1 \leq \tfrac16 \log\log b$. On a ruler that measures $\log$ of each quantity, the picture changes: $\log x$ is small, $\log x_1$ is at least $10^6$ times larger, and $\log b$ is again at least $10^6$ times larger. The ranks, the degree of the field, the root discriminant and the gap live between $\tfrac12 \log x$ and $41 \log x$ on the second ruler. All the weights, the primes $p_0$, $p_1$, the level $M$ and the prime $N$ live at $\log b$ or beyond.

The argument works at two levels. At the level of $x$, it handles the combinatorics: the ranks, the field, the number of lifts. At the level of $b$, it handles the analysis: the weights of the automorphic forms, the levels, and the error terms of the covolume. The scale $x_1$ sits between them. It cuts the prime sum at a second point, and the prime number theorem makes the remainder at $x_1$ negligible.

### How the table is organized

Section 3 has the table. It has six groups of rows: the parameters, the scales, the ranks, the field, the weights, and the primes with the level. A row gives

1. the quantity, in the notation of [notation and conventions](/chapter/notation/);
2. the bound, exactly as Lean states it, with the same constants and the same form of interval;
3. the Lean declaration with its full namespace, and the file and the line where it is stated;
4. a short note on where the argument uses the bound.

A file name without a folder is in `New/Reduction/Data/`. Line numbers are at the pinned commit of the source. Where a bound is an instance of the size automation, the row says "instance" and gives the line of the instance, since an instance has no name that a reader can cite.

### What the chapter uses and what it proves

The chapter states no new result. Each bound in it is a lemma of the source, a field of a structure of the source, or an instance of the size automation of the source. The proofs are in Volume 1 and in the chapters that use each bound. Where this chapter gives a reason, for example why a gap is large, the reason is an observation about the sizes of the source, and the text says which comparison of the source it comes from. The source itself does not explain its choice of constants. So the explanations in Section 7 are the reading of this book, not claims of the source.

The bounds are statements about any data $D$. Lean accepts them, if the reported checks hold. The chapter does not claim that the argument is correct.

### The plan

Section 2 states the five scale inequalities and the constant $C_P$. Section 3 is the table. Section 4 shows how the source builds data with these sizes, and gives the exact values of $x_1$, $b$, $m$ and $r$ in that construction. Section 5 gives the error budget of the main inequality and the step from it to the exponent $-\tfrac12 + \varepsilon$. Section 6 lists the size conditions that later parts of the argument impose, such as $10^5 \leq \varrho$ in the filling data and $10^8 \leq \varrho$ at the real places, and shows how the data meet them. Section 7 explains the order of the scales and the size of each gap. Section 8 has the exercises and the notes.
