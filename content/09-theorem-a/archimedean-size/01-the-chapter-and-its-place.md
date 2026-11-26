---
title: The chapter and its place
lean:
  - New/UpperBound/Size/ClassCount.lean
  - New/UpperBound/Size/Estimates.lean
  - New/UpperBound/Size/ArchimedeanSize.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapter and its place

This chapter proves the size side of Theorem A. Let $\Psi$ be a chain datum for the trivial twist, and let $\varphi$ be a source form whose values have squared Weyl norm at most $e^B$ after an automorphism $\sigma$ of $\mathbb C$. The theorem of the chapter says that the values of the composite lift $B_{1,\Psi}\varphi$ have squared Weyl norm at most $\exp(B + \beta)$, with
$$\beta = \mathrm{main} - m\cdot\mathrm{rem} + 2\sum_{p\in\mathcal S}\mathrm{gain}_p\log p + f a\log^3 b .$$
Here $\mathcal S$ is the set of primes $p < x_1$ that do not split in $K = \mathbb Q(\sqrt{-d})$. The chapter also proves three groups of tools for the rest of the argument: explicit counts of classes $\Gamma\backslash G_f/K$, a bound for the sum of the allowed losses, and two lemmas on the good part $|\mathsf G|e_0 s z$ of a form on $Y_0$.

### Where the chapter sits

The plan of the book is in [the theorem and the plan](/chapter/theorem-and-plan/), and the plan of Theorem A is in [Theorem A and its plan](/chapter/theorem-a-plan/). Theorem A has three inputs: the divisibility of the composite lift prime by prime, the seesaw identity, and the archimedean size. [The three inputs](/chapter/theorem-a-plan/#the-three-inputs) states the third input. This chapter proves it.

The objects of the chapter are in [the objects of the upper bound](/chapter/upper-bound-objects/): the spaces $X_j$ and $Y_m$, the weights and the lift diagrams, the lift kernels, the chain data, the restriction to $Y_m$ and the lower chain. The chain of lifts as a plain sum over classes, the restriction bound and the expansion of the glued tensor are in [marked primes and the valuation of a chain](/chapter/chain-valuation/). The bound for the jets of one kernel is in [theta kernels and gauges](/chapter/theta-kernels-gauges/). The local prime sums $s_p$, the gain and the loss are defined in [short columns and the gain](/chapter/short-columns-gain/). The chapter [the proof of Theorem A](/chapter/proof-of-theorem-a/) puts the size bound, the divisibility and the seesaw identity together.

### What the chapter uses

The data $D$ and their sizes are those of [the data and their sizes](/chapter/data-and-sizes/). The chapter cites the rows of [the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes) by name. It uses most often: $a = xb$ with $x^{999} \le a/x_1$; $\kappa(\tau) \le b$ and $\kappa(\tau) \geq a/x_1$; $f \le q_1 \le x^{12}$; $n_m \le e^{12}x^{11/2}$; $\tfrac12\Delta = r^8$ with $k + t + 1 \le r^8$; $20\log b \le \log(M/\Omega) \le 23\log b$; $|\log(M\,\mathrm{rd}_E/2\pi)| \le 23\log b$; $\log N \le 30m\log b$; and $\mathrm{err}_0 = f a\log^3 b$. The prime sums $s_{\mathrm{fin}}$, the jet size $s_\infty$, the main amount, the expected value $s_{\mathrm{main}}$ and the total remainder are in [the prime sums](/chapter/prime-sums/).

From earlier volumes the chapter uses:

- the class sets $\Gamma\backslash G_f/K$, the class sum and the norm $\|\varphi\|^2_\sigma$, from [automorphic forms](/chapter/automorphic-forms/);
- short bases of the standard lattice in each class, from [reduction theory](/chapter/reduction-theory/);
- the levels $K_0$ and $K(\mathfrak a)$, from [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/);
- the Gram norm $\|\xi\|_{\mathrm W}$ of a vector of a Weyl module and its triangle inequality, from [Weyl modules](/chapter/weyl-modules/);
- central idempotents of a group algebra and their coefficients, from [congruence subgroups](/chapter/congruence-subgroups/);
- the different of $E$, from [CM fields](/chapter/cm-fields/).

Two results come from Volume 10: the approximation of finite adeles by bounded elements of $E$ and the count of bounded integral vectors. Both are in [the anatomy of a term](/chapter/anatomy-of-a-term/). This chapter states them with a short proof where it uses them. No file of this chapter imports a file of a later chapter of Volume 9.

### The sketch

The composite lift is a chain of $m$ theta lifts $X_0 \to X_1 \to \dots \to X_m$, followed by the restriction to $Y_m$. [Marked primes and the valuation of a chain](/chapter/chain-valuation/#expanding-the-gluing) turns a chain datum into a weak chain datum $\Psi'$ with the same lift. So it is enough to bound the restricted chain of a weak chain datum. A value of the restricted chain is a sum of four kinds of factors.

1. *One kernel.* The lift from $X_j$ to $X_{j+1}$ multiplies the Weyl norm by at most $\exp(x^{50} + \tfrac12\mathrm{rowSize}_j)$. Here $\mathrm{rowSize}_j$ is the sum of $s_\infty(l)$ over the row lengths $l$ of the Young diagram of the weight of the lift. This comes from the bound for Schur jets of [theta kernels and gauges](/chapter/theta-kernels-gauges/).
2. *The terms.* A value of the chain is a sum over classes of $\prod_j \Gamma_j\backslash G_j/K_j$ and over the support of $\Psi'$. The class count is at most $\exp(x^{30})$ at each stage. The coefficients add up to at most $\exp(x^{60})$.
3. *The restriction.* The restriction to $Y_m$ divides the squared norm by $N^{\sum_\tau n_\tau}$, with $\sum_\tau n_\tau = \#\Phi_a a - fm\Delta/2$. It also multiplies it by at most $\exp(x^{70})$.
4. *The exponent.* The sum of the row sizes over the $m$ lifts is at most $\mathrm{chainSize} + \tfrac12 f a\log^3 b$. The prime sums then cancel: $\mathrm{chainSize} - \#\Phi_a a\log N$ is at most $\mathrm{main} - m\cdot\mathrm{rem} + 2\sum_p\mathrm{gain}_p\log p + 32 fa\log b$.

All the powers of $x$ are tiny against $f a\log^3 b$, since $a \ge x^{999}x_1$. So they go into the error.

The sections follow the needs of this proof. Section 2 counts the classes of the standard level $K_0$. Section 3 turns this count into the bounds $\exp(x^{29}(1 + \log G))$ and $\exp(x^{30})$ at the data. Section 4 groups the prime sums by primes and bounds the sum of the allowed losses. Section 5 bounds the rows of the lift diagrams and the size of one kernel. Section 6 computes the exponent. Section 7 proves the theorem on the size of the composite lift. Section 8 proves two lemmas on the good part. Section 9 has exercises and notes.

### The model case

[A model case](/chapter/theorem-a-plan/#a-model-case) explains the shape of the bound with one lift and one place. The jet of order $l$ of a theta kernel at an archimedean place has size about $l!\,(M/\Omega)^l$, since a derivative of order $l$ of a Gaussian brings down $l$ factors of the variable and the scale is $M/\Omega$. So its logarithm is $s_\infty(l) = \log l! + l\log(M/\Omega)$, and this is the meaning of the jet size. The norm of a vector of the Weyl module grows like the square root of the product of the jet sizes, which explains the factor $\tfrac12$ in $\tfrac12\mathrm{rowSize}_j$.

In the model case the divisibility side gives the prime sum $s_{\mathrm{fin}}(l, \tau)$ at a row of length $l$, and the difference $s_\infty(l) - s_{\mathrm{fin}}(l,\tau)$ is what remains. The level $N$ is chosen in [the data and their sizes](/chapter/data-and-sizes/#the-primes-the-level-and-the-period) so that the restriction removes the excess of the first rows. This chapter carries out the same count for all the rows, all the places and all the $m$ lifts at once.

### Conventions

The notation is that of [the objects of the upper bound](/chapter/upper-bound-objects/). The letter $\Phi$ is the set of the $f$ infinite places of $E$, and $\Phi_a \subset \Phi$ is the set of $a$-places. The number $a_\tau$ is $a$ if $\tau \in \Phi_a$ and $0$ otherwise. For a weight, $c_\tau(h)$ is the number of columns of height $h$ at $\tau$, so $c_\tau(1) = a_\tau$. The Gram norm of a vector $\xi$ of a Weyl module is $\|\xi\|_{\mathrm W}$, and $\|\xi\|^2_{\mathrm W}$ is the squared Weyl norm. For $\sigma \in \mathrm{Aut}(\mathbb C)$, $\sigma\circ\xi$ is the vector of the $\sigma(\xi_i)$. The letter $r$ is the rank of the data, $r = 3^{e+1}$, except in Section 2, where it is the size of an index set.
