---
title: Liouville's inequality
lean:
  - New/Reduction/Lattices/Heights.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Liouville's inequality

This section works out the lower bound of the method in rank one. A nonzero algebraic integer cannot be small at every archimedean place. The proof is the product formula. Liouville's theorem on rational approximation follows from it, and the section does the example $\sqrt 2$ in full.

### The product formula

Let $K$ be a number field of degree $n_K = [K : \mathbb{Q}]$. For a place $v$ of $K$ let $|\cdot|_v$ be the absolute value on $K$ that extends the usual absolute value of $\mathbb{Q}$ at the place below $v$, and let $n_v = [K_v : \mathbb{Q}_p]$ be the local degree, with $\mathbb{Q}_\infty = \mathbb{R}$. Then $\sum_{v \mid p} n_v = n_K$ for each $p \leq \infty$.

**Theorem (Product formula).** For every $\alpha \in K^\times$,
$$\sum_v n_v \log |\alpha|_v = 0,$$
where the sum runs over all places of $K$ and has only finitely many nonzero terms.

This is in Neukirch, *Algebraic Number Theory*, Chapter III, §1. It follows from the case $K = \mathbb{Q}$, which is unique factorization, because $\prod_{v \mid p} |\alpha|_v^{n_v} = |N_{K/\mathbb{Q}}(\alpha)|_p$ for each $p \leq \infty$.

The archimedean places of $K$ correspond to the embeddings $\sigma\colon K \to \mathbb{C}$ up to complex conjugation, and $\sum_{v \mid \infty} n_v \log|\alpha|_v = \sum_\sigma \log|\sigma \alpha|$. So the product formula splits into a part at infinity and a part at the primes:
$$\sum_{\sigma\colon K \to \mathbb{C}} \log |\sigma \alpha| = - \sum_{v \nmid \infty} n_v \log |\alpha|_v .$$
The left side measures the size of $\alpha$. The right side measures its denominators: it is $\leq 0$ if $\alpha$ is integral at every prime.

### A nonzero algebraic integer is not small everywhere

**Proposition (Liouville's inequality).** Let $\alpha \in K^\times$. Then
$$\max_{\sigma\colon K \to \mathbb{C}} \log |\sigma\alpha| \geq \frac{1}{n_K} \sum_\sigma \log|\sigma \alpha| \geq - \frac{1}{n_K}\sum_{v \nmid \infty} n_v \log^+ |\alpha|_v ,$$
where $\log^+ t = \max(0, \log t)$. If $\alpha$ is an algebraic integer, the right side is $0$, and $\prod_\sigma |\sigma\alpha| = |N_{K/\mathbb{Q}}(\alpha)| \geq 1$.

*Proof.* The first inequality says that the maximum is at least the mean. The second is the split product formula with $\log|\alpha|_v \leq \log^+|\alpha|_v$. For an algebraic integer, $N_{K/\mathbb{Q}}(\alpha)$ is a nonzero rational integer, so its absolute value is at least $1$. $\square$

The bound is for the largest conjugate, not for $\alpha$ itself: $\sqrt 2 - 1 \approx 0.414$ is small, but its conjugate has absolute value about $2.414$. Integrality at every prime is used. If $D\alpha$ is an algebraic integer for an integer $D \geq 1$, the bound becomes $\prod_\sigma |\sigma\alpha| \geq D^{-n_K}$. A denominator costs exactly its logarithm. In the source the denominators are the index of a family in a lattice (Section 5), and they enter the inequality with this cost.

### Liouville's theorem

**Theorem (Liouville, 1844).** Let $\alpha \in \mathbb{R}$ be algebraic of degree $n \geq 2$. Then there is $c(\alpha) > 0$ such that
$$\Bigl|\alpha - \frac{p}{q}\Bigr| \geq \frac{c(\alpha)}{q^n}$$
for all integers $p$ and $q \geq 1$.

*Proof.* Let $F \in \mathbb{Z}[X]$ be the minimal polynomial of $\alpha$ with coprime integer coefficients and leading coefficient $c_n > 0$. It is irreducible of degree $n \geq 2$, so it has no rational root, and $q^n F(p/q)$ is a nonzero integer. So $|F(p/q)| \geq q^{-n}$. If $|\alpha - p/q| \geq 1$, any $c(\alpha) \leq 1$ works. Otherwise the mean value theorem gives $\xi$ between $\alpha$ and $p/q$ with
$$|F(p/q)| = |F(p/q) - F(\alpha)| = |F'(\xi)|\,|\alpha - p/q| \leq M |\alpha - p/q|, \qquad M = \max_{|t - \alpha| \leq 1} |F'(t)|.$$
So $|\alpha - p/q| \geq 1/(M q^n)$. Take $c(\alpha) = \min(1, 1/M)$. $\square$

The proof is the proposition above in disguise. Let $K = \mathbb{Q}(\alpha)$ and $\beta = q\alpha - p$. Then $\beta \neq 0$, $c_n \beta$ is integral at every prime (since $c_n\alpha$ is an algebraic integer), and
$$N_{K/\mathbb{Q}}(\beta) = \prod_{i=1}^n (q\alpha_i - p) = (-1)^n \frac{q^n F(p/q)}{c_n},$$
where $\alpha_1 = \alpha, \alpha_2, \dots, \alpha_n$ are the conjugates. One conjugate, $|\beta| = q|\alpha - p/q|$, is small. The others are at most $q|\alpha_i - \alpha| + q$ when $|\alpha - p/q| \leq 1$, and the denominator $c_n$ is fixed. So the small conjugate is at least about $q^{-(n-1)}$, and this is the theorem.

### The example $\sqrt 2$

Let $\alpha = \sqrt 2$, so $F = X^2 - 2$ and $n = 2$. For integers $p$ and $q \geq 1$, the integer $p^2 - 2q^2$ is not $0$, so $|p^2 - 2q^2| \geq 1$. Thus
$$\Bigl|\sqrt 2 - \frac pq\Bigr| = \frac{|p^2 - 2q^2|}{q^2\,(\sqrt 2 + p/q)} \geq \frac{1}{q^2\,(\sqrt 2 + p/q)}$$
for $p > 0$. If $|\sqrt 2 - p/q| \leq 1$, then $p/q \leq \sqrt 2 + 1$, and
$$\Bigl|\sqrt 2 - \frac pq\Bigr| \geq \frac{1}{(2\sqrt 2 + 1)\, q^2} .$$
In the language of the proposition, $\beta = p - q\sqrt 2 \in \mathbb{Z}[\sqrt 2]$ has the conjugate $p + q\sqrt 2$, and $|\beta| \cdot |p + q\sqrt 2| = |p^2 - 2q^2| \geq 1$.

The convergents of the continued fraction of $\sqrt 2$ show how sharp this is. Here are three of them, with $q^2|\sqrt 2 - p/q|$ to three digits:

| $p/q$ | $\lvert\sqrt 2 - p/q\rvert$ | $q^2 \lvert\sqrt 2 - p/q\rvert$ |
|---|---|---|
| $3/2$ | $0.0858$ | $0.343$ |
| $7/5$ | $0.0142$ | $0.355$ |
| $17/12$ | $0.00245$ | $0.353$ |

Each convergent has $|p^2 - 2q^2| = 1$. So $q^2|\sqrt 2 - p/q| = 1/(\sqrt 2 + p/q)$, and this tends to $1/(2\sqrt 2) \approx 0.354$. The bound $1/(2\sqrt 2 + 1) \approx 0.261$ of the proof is weaker only by the crude step $p/q \leq \sqrt 2 + 1$. So the inequality is sharp up to a constant here.

### The lesson for the method

The proof compares two bounds for one nonzero number $N(\beta)$: integrality gives $|N(\beta)| \geq 1$, and size gives an upper bound, small because one factor is small. In the source the number is a Gram determinant. Integrality, corrected by the index, gives the lower bound (Theorem C), and short vectors give the upper bound (Theorem A).

The source states the rank-one inequality for complex numbers with heights over all isomorphisms $\mathbb{C} \cong \bar{\mathbb{Q}}_\ell$, not over the places of a fixed number field. The statements are [Theorem](/decl/New.HeightLe.nonneg_of_one/) (a family of height at most $c$ equal to $1$ has $c \geq 0$) and [Corollary](/decl/New.HeightLe.neg_le_of_norm_map_le/) (if $z \neq 0$ has height at most $c$ and $|\sigma z| \leq e^{c'}$ for every automorphism $\sigma$ of $\mathbb{C}$, then $-c \leq c'$). They are proved in [twisted lattices](/chapter/twisted-lattices/), together with the version for Gram determinants.

**Remark (Formalization).** The source does not use the product formula of a number field. It proves the product formula for $\mathbb{Q}$ only (`New.log_product_formula`), and it reaches algebraic numbers through the norm to $\mathbb{Q}$, as in the proof of the proposition above. Its heights allow a number $y_\iota$ that changes with $\iota$ and a common multiplier $H$. For a constant family the definition reduces to the proposition above, with $H$ in the role of the denominator $D$.
