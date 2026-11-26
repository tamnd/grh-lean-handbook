---
title: The idea of the method
lean:
  - New/Reduction/MainInequality.lean
  - New/Reduction/OneSidedBound.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The idea of the method

The analytic part of the plan is classical in form: a one-sided bound for a weighted prime sum gives a zero-free half-plane. The new part is the source of the bound. The source builds an integral lattice of automorphic forms and bounds its covolume twice: from above with short vectors, and from below with heights and the product formula. Both bounds contain the same main amount. The prime sum is in their difference. This section has no proofs. [Why a lattice can bound a prime sum](/chapter/lattice-and-prime-sum/) gives the full account, and the exact statements are in Section 2.

### Size against divisibility

The model is Liouville's inequality. A nonzero integer $N$ has $|N| \geq 1$. So if $p^{e_p}$ divides $N$ for each prime $p$ of a finite set, then
$$\sum_p e_p \log p \leq \log |N|.$$
An upper bound for the size of $N$ bounds how often primes divide $N$. The product formula is the same fact in a form that works for every nonzero rational number $\alpha$: $\log|\alpha|_\infty + \sum_p \log |\alpha|_p = 0$. If $\alpha$ is integral, each $\log|\alpha|_p \leq 0$, and the archimedean term makes up for the divisibility.

Here is the shape of the argument in rank one. Suppose that a construction gives a nonzero integer $N$, divisible by $p^{g_p}$ for each prime $p$, and suppose that
$$\sum_p g_p \log p = S, \qquad \log|N| \leq A.$$
Then $S \leq A$. Now suppose that $S$ is a weighted sum over primes, and that $A = \mathbb{E} + e$, where $\mathbb{E}$ is the expected value of $S$ and $e$ is an error. Then
$$S - \mathbb{E} \leq e.$$
This is a one-sided bound for the remainder of a prime sum. It is useful only if $e$ is much smaller than $\mathbb{E}$, so the size bound must know the main term to the precision $e$. The source meets this need by computing one main amount in two ways that agree up to the error.

### Lattices, covolumes and Hadamard

In rank $n$ the integer $N$ becomes a Gram determinant. Let $y_1, \dots, y_n$ be linearly independent vectors of $\mathbb{Z}^{M}$, and let $G = \det(\langle y_i, y_j \rangle)$. Then $G$ is a positive integer, so $\log G \geq 0$. Hadamard's inequality gives $G \leq \prod_i \|y_i\|^2$. So if $\|y_i\|^2 \leq e^{L}$ for each $i$, then
$$0 \leq \log G \leq nL.$$
The covolume $\log G$ has a lower bound from integrality and an upper bound from short vectors. If the vectors are integral only up to denominators, the lower bound loses the logarithm of the index, twice, because $G$ is quadratic in the vectors. [Twisted lattices](/chapter/twisted-lattices/) proves the inequality in the setting of the source, from the product formula, and in the form
$$c + 2\delta \geq (\text{a term that the lattice fixes}),$$
where $c$ bounds the covolume at every archimedean place and $\delta$ bounds the index.

In the source the vectors are automorphic forms, and the structure is a *twisted lattice*: for each twist $\xi$, a linear map $\Theta_\xi$ to an inner product space with integral vectors at each prime. The twist $1$ gives the sizes at the automorphisms $\sigma$ of $\mathbb{C}$. The twists $\xi_\iota$, one for each isomorphism $\iota\colon \mathbb{C} \cong \overline{\mathbb{Q}}_\ell$, give the valuations.

### The two bounds

The space is the space of target forms of the data $D$, of dimension $d_T$. Theorems A and B give a family $y_1, \dots, y_n$ of target forms with $n \geq (1 - 4/b^2)d_T$. Each $y_i$ is the image of a short integral source form under a translate $s\mathfrak{p}$ of one map $\mathfrak{p}$, built from Poincaré series.

The upper bound comes from short vectors. Theorem A(a) says that each lift is short: $\log \|\Theta_1 y_i\|_\sigma^2 \leq \mathrm{mainAmount} - m\,\mathrm{rem} + f a \log^4 b$ at every $\sigma$. By Hadamard, the covolume of the family is at most $n(\mathrm{mainAmount} - m\,\mathrm{rem} + f a \log^4 b)$. Theorems A(b) and B bound the index by $d_T$ times a small error.

The lower bound comes from heights. Theorem C says that every such family has
$$\text{covolume} + 2\cdot\text{index} \geq d_T(\mathrm{mainAmount} - 3 f a \log^4 b).$$
Its proof applies the product formula to a Gram determinant, with sizes read with the twist $1$ and valuations read with the twists $\xi_\iota$. It needs a bound for the height of the ratio $Z(1)/Z(\xi_\iota)$ of the volumes of $\Theta_1$ and $\Theta_{\xi_\iota}$. Volumes 11 and 12 prove this bound.

Put the two bounds together with $n \approx d_T$. The term $d_T \cdot \mathrm{mainAmount}$ is on both sides, and it cancels. What is left is
$$n\, m\, \mathrm{rem} \leq d_T \cdot (\text{errors}),$$
which is the star inequality $m\,\mathrm{rem} \leq f a \log^5 b$ of Section 2.

### The same main amount

The main amount is $m k$ times the cost of one direction, where $k$ is the rank of the space $X_0$ of the source forms. The method works only because it enters both bounds with the same value, not merely with the same order of size. In the upper bound it is the archimedean size of the lifts, which the source compares with the expected value of the prime sums. In the lower bound it enters through the height of $Z(1)/Z(\xi_\iota)$, where the volume is a chain determinant ([the lattice of integral target forms](/chapter/integral-target-forms/)). The head of the file of the main inequality lists what cancels:

- the main amount, between Theorems A and C;
- the gains $\sum_\ell \mathrm{gain}_\ell \log \ell$, against $\log c_B$, where $c_B$ is a normalizing constant;
- the constant $c_1$, between the period and the expected value of the prime sums;
- the excesses of the $m$ lifts, against $a \log N$, up to $O(a \log b)$;
- the main terms of the prime sums, in the identity for $\mathrm{rem}$;
- a constant that depends on $q_0$, between the cut-offs $x$ and $x_1$.

The errors that remain are in the table of the same file. They are, per dimension, $f a \log^4 b$ for the size, $20 \log(1 + 2b^2) \cdot f a \log^3 b$ for the index (the index enters twice), and $3 f a \log^4 b$ for the covolume. Twice their sum is at most $f a \log^5 b$, because $\log b$ is large.

### Where the primes enter

The prime sums enter through divisibility, as in the model of rank one. The glossary of the source defines the prime sum at an order $y$ and a place $\sigma$ as
$$\sum_{1 \leq \nu \leq a} \Lambda(\nu)\bigl(1 - \chi_K(\nu)\bigr)\Bigl(\frac{y}{\nu} - \kappa(-\nu\sigma)\Bigr)_+,$$
where $\kappa$ is the weight of a place. Its part at a prime $p$, divided by $2 \log p$, is the *local prime sum* $s_p(y, \sigma)$. The *gain* at $p$ is the exponent of $p$ that the proof asks to divide the chain of $m$ lifts. The source defines it as
$$\mathrm{gain}(p) = m\Bigl(\sum_{\tau \in \Phi_a} s_p(a, \tau) + k\, F(p)\Bigr),$$
where $F(p)$ is the sum of the local prime sums over all infinite places ([ShortColumns.lean](lean:New/UpperBound/Size/ShortColumns.lean#L83)). So the more often the primes of the sum occur, the more the lifts are divisible, and the shorter the forms are after division. The first part of the gain, weighted by $2\log p$ and summed over $p$, is $m$ times the prime sums at the places of $\Phi_a$, and $\mathrm{rem}$ is these prime sums less their expected values. This is why $m\,\mathrm{rem}$ enters the bound of Theorem A(a) with a minus sign. The weights $1 - \chi_K(\nu)$ are those of the weighted prime remainder of Section 2. They are $0$ at the primes that split in $K = \mathbb{Q}(\sqrt{-d})$ and $2$ at the inert primes.

The sign has a consequence. A large positive $\mathrm{rem}$ would make the family too short for the lower bound of Theorem C. A large negative $\mathrm{rem}$ gives no contradiction. So the method bounds $\mathrm{rem}$ from above only. This is enough, because the weights $\lambda(n)$ are nonnegative, and Landau's criterion needs a bound on one side only.

### Why the exponent stops at 1/2

The exponent $1/2$ comes from one place: the term $\varphi(q_0)\log^6 b/m$ in [Theorem](/decl/New.Data.primeRemainder_le/). The rest of that bound is far smaller, because the terms at $x_1$ are controlled by the prime number theorem and $x_1 \geq x^{10^6}$. The data fix $m$ in $[\sqrt{x}, 2\sqrt{x}]$, and the end of the proof takes $\log b \leq 2x^{\varepsilon}$. So the method gives
$$R_{q_0}(x) \ll x^{-1/2 + 6\varepsilon}.$$
The factor $m$ is the number of lifts in the chain $Y_0 \to Y_m$, and it multiplies the prime sums in the gain. Dividing the star inequality by $m$ gives the factor $1/m$ in the bound for $R_{q_0}(x)$. Suppose that the same steps worked with $m \approx x^{\theta}$. Then they would give $R_{q_0}(x) \ll x^{-\theta + 6\varepsilon}$, and Landau's criterion would give no zeros only in $\operatorname{Re} s > 1 - \theta$. With $\theta = 1/2$ this is the half-plane of the generalized Riemann hypothesis.

So $1/2$ is the exponent of $x$ in $m$. In the explicit formula of [the weighted prime remainder](/chapter/weighted-prime-remainder/), a zero $\rho$ of an L-function modulo $q_0$ or of a twist by $\chi_K$ gives a pole of the Mellin transform of $R_{q_0}$ at $\rho$, that is, a term of size $x^{\operatorname{Re}\rho - 1}$. If all these zeros were on the line, the terms would have size $x^{-1/2}$. So the bound of the source has the size that the generalized Riemann hypothesis predicts, up to the factor $x^{6\varepsilon}$.

The data tie $m$ to the other scales. The number $m$ is a power of $2$ with $2^{s} = m^{22}$, where $s$ is the exponent of a tower of fields, and the rank $r$ lies in $[x^5, 3x^5]$. Theorem C also has conditions that involve $m$, $x_1$ and $b$. The source does not say in one place which of these conditions, or which step of the proofs of Theorems A, B and C, prevents a larger $m$. This book leaves the question open. [The data and its sizes](/chapter/data-and-sizes/#the-table-of-sizes) gives the table of the scales.
