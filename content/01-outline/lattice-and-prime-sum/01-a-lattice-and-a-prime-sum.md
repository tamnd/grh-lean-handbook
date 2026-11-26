---
title: A lattice and a prime sum
lean:
  - New/Reduction/MainInequality.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## A lattice and a prime sum

This chapter explains the idea of the method of the source. It proves few results of the source. It works out three model cases in full, and it states the main inequality of the source with its proof from Theorems A, B and C. The later chapters of this volume and Volumes 9 to 11 give the full definitions and proofs.

### Where the chapter sits

[The plan](/chapter/theorem-and-plan/) of the proof has three layers. At the top, [Landau's criterion](/chapter/landau-criterion/) turns a one-sided bound for a weighted sum over primes into the absence of zeros of L-functions in the half-plane $\operatorname{Re} s > 1/2$. The bound that it needs is
$$R_{q_0}(y) \leq y^{-1/2 + \eta} \qquad \text{for all large real } y,$$
for each $\eta > 0$, where $R_{q_0}$ is [the weighted prime remainder](/chapter/weighted-prime-remainder/). In the middle, the main inequality of the source gives this bound. At the bottom, Theorems A, B and C give the main inequality. This chapter explains why a lattice, a geometric object, can bound a sum over primes.

### The idea in one paragraph

A nonzero integer has absolute value at least $1$. The argument has no other source of lower bounds. The source applies it, through the product formula, to a Gram determinant: the squared covolume of a family of $n$ vectors $y_1, \dots, y_n$ in a lattice of rank $d_T$, the space of target forms. There are two bounds for this one number. In them $\mathrm{main}$ is the main amount and $\operatorname{rem}$ is the total remainder of Section 5.

1. The upper bound. The vectors are short. Theorem A gives forms whose squared length at every conjugate is at most $\exp(\mathrm{main} - m \operatorname{rem} + f a \log^4 b)$, and Theorem B says that the translates of these forms span almost all of the target. Hadamard's inequality bounds the squared covolume of $n$ short vectors by the product of their squared lengths: at most $\exp\bigl(n(\mathrm{main} - m \operatorname{rem} + f a \log^4 b)\bigr)$.
2. The lower bound. The vectors are integral. Theorem C says that integral forms are long: the squared covolume, corrected by the index, is at least $\exp\bigl(d_T(\mathrm{main} - 3 f a \log^4 b)\bigr)$. Its proof is the product formula for one algebraic number.

The main amount is the same in both bounds. It is very large, at least $x^4 f a$. When $n$ is close to $d_T$, the two bounds give
$$n \, m \operatorname{rem} \leq d_T \cdot (\text{errors}),$$
and the main amount cancels. The total remainder $\operatorname{rem}$ is a sum over primes less its expected value. It is multiplied by the number $m$ of theta lifts, while the errors do not grow with $m$. This gives
$$m \operatorname{rem} \leq f a \log^5 b .$$
The prime sum enters the upper bound through divisibility. The forms of Theorem A are divisible by large powers of the small primes, and the source divides these powers out. The more primes there are, the shorter the forms after the division. So a large positive remainder would make the forms too short to be integral. This is why the bound has one side only.

### The words of the idea

Here are the objects of the paragraph above, in the words of the source. The exact definitions are in [the data and its sizes](/chapter/data-and-sizes/).

- The data $D$ fix three scales $x \leq x_1 \leq b$, each enormous against the one before, and the long order $a = x b$.
- The field $E = K(\zeta_{q_1})$, with $K = \mathbb{Q}(\sqrt{-d})$ and $q_1 = q_0 \cdot \mathrm{towerDeg}(s)$ for the tower exponent $s$ ([the fields, the places and the twists](/chapter/fields-places-twists/)), has $f$ infinite places, and two sets $\Phi_a$ and $\Phi_b$ of them carry special weights.
- The number $m$ of theta lifts in a chain is a power of $2$ with $\sqrt x \leq m \leq 2\sqrt x$ ([the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes)).
- The target forms are a complex vector space of dimension $d_T$ with an integral structure at every prime: a twisted lattice ([twisted lattices](/chapter/twisted-lattices/)).
- The main amount compares the size $s_\infty$ of a derivative with the prime sum $s_{\mathrm{fin}}$ that measures its divisibility (Section 5).
- The total remainder $\operatorname{rem}$ is $\sum_{\tau \in \Phi_a} \bigl(s_{\mathrm{fin}}(a, \tau) - s_{\mathrm{main}}\bigr)$, a sum of prime sums less their expected value $s_{\mathrm{main}}$.

### Three model cases

- Liouville's inequality (Section 2). A nonzero algebraic integer cannot be small at every archimedean place. This is the product formula for one number, and it is the lower bound of the method in rank one.
- A toy model (Section 3). A positive sum over primes is bounded by two bounds for one integer: the central binomial coefficient. The upper bound for the sum comes from divisibility against size, as in the source. The main terms cancel, as in the source.
- The slope inequality (Section 4). The degree of a Euclidean lattice is bounded above by the slopes of a target and the height of a map. It is the standard form of the lower bound of the source, Theorem C.

Section 5 then gives the two bounds of the source and the proof of the main inequality. Section 6 explains why the result stops at the exponent $1/2$. Section 7 has exercises and the notes.

### What the chapter uses

The chapter uses the product formula of a number field (Neukirch, *Algebraic Number Theory*, Chapter III, §1), Hadamard's inequality for a positive semidefinite matrix, and Stirling's formula for $\log n!$. Sections 1 to 4 do not need the definitions of the source. The forward results in Section 5 are stated in full, with links to the chapters that prove them.

The main inequality of Section 5 is a theorem of the source. Lean accepts its proof from Theorems A, B and C, and the proofs of these theorems, if the checks that the source reports hold. This book did not rerun the checks (Volume 0, Chapter 2).
