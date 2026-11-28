---
title: The classical theory
lean:
  - New/Reduction/Data/Existence.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The classical theory

This section gives the classical theory of sets with no three-term progressions. It has two halves. The lower bounds are constructions: the digit sets of Erdős and Turán and the spheres of Behrend. The source uses Behrend's construction, and this section proves it in full. The upper bounds start with the theorem of Roth. The source does not use them, but they tell the reader that the constructions are close to the truth and that a set of positive density is impossible. The last part treats equations with weights, which is the form that the argument needs.

### The Roth number

A *three-term progression* in a set $A$ of integers is a triple $(a, b, c) \in A^3$ with $a + c = 2b$. It is *trivial* if $a = b = c$. A set is *free of three-term progressions*, or *3AP-free*, if all its three-term progressions are trivial. Equivalently, $A$ contains no $\{a, a + h, a + 2h\}$ with $h \neq 0$.

**Definition (Roth number).** For an integer $N \geq 0$, $r_3(N)$ is the largest size of a 3AP-free subset of $\{0, 1, \dots, N - 1\}$.

Mathlib: `ThreeAPFree` (Mathlib) and `rothNumberNat` (Mathlib). The predicate `ThreeAPFree s` says that $a + c = b + b$ with $a, b, c \in s$ implies $a = b$. The function `rothNumberNat N` is the largest size of a 3AP-free subset of `range N`, that is, of $\{0, \dots, N - 1\}$. It is monotone in $N$.

The function $r_3$ does not change under translation and dilation, so a 3AP-free subset of any progression of length $N$ has at most $r_3(N)$ elements. The question of Erdős and Turán is the size of $r_3(N)$. Since $r_3$ is subadditive, $r_3(N)/N$ has a limit. The theorem of Roth says that the limit is $0$. The best constructions give $r_3(N) = N^{1 - o(1)}$. The truth lies between $N \exp(-c\sqrt{\log N})$ and $N \exp(-c'(\log N)^{1/9})$.

### The digit sets of Erdős and Turán

Erdős and Turán introduced the problem in 1936. Their example is the set of integers with ternary digits $0$ and $1$.

**Proposition (Erdős and Turán).** Let $n \geq 0$, and let $S_n$ be the set of integers $a = \sum_{i < n} a_i 3^i$ with all $a_i \in \{0, 1\}$. Then $S_n \subseteq \{0, \dots, 3^n - 1\}$ is 3AP-free and $\# S_n = 2^n$. So $r_3(3^n) \geq 2^n$, and $r_3(N) \geq \tfrac12 N^{\log 2/\log 3}$ for all $N \geq 1$.

Not in the source. The source does not use base $3$. It uses the sets of Behrend with weights, [Behrend's sets](/decl/New.exists_three_term_free/).

*Proof.* Let $a, b, c \in S_n$ with $a + c = 2b$. The digits $a_i + c_i$ and $2 b_i$ lie in $\{0, 1, 2\}$, so both sums are written in base $3$ without carries. The expansion in base $3$ is unique, so $a_i + c_i = 2 b_i$ for each $i$. If $b_i = 0$ this gives $a_i = c_i = 0$, and if $b_i = 1$ it gives $a_i = c_i = 1$. So $a = b = c$. For $3^n \leq N < 3^{n+1}$ the monotonicity of $r_3$ gives $r_3(N) \geq 2^n = (3^n)^{\log 2/\log 3} > (N/3)^{\log 2/\log 3} \geq \tfrac12 N^{\log 2/\log 3}$. $\square$

The density of $S_n$ in $[0, 3^n)$ is $(3^n)^{-(1 - \log 2/\log 3)} = (3^n)^{-0.369\ldots}$. Erdős and Turán asked whether $r_3(N)$ is of the order $N^{\log 2/\log 3}$. Salem and Spencer answered this in 1942. They took integers whose digits in a large base $B$ lie below $B/2$, so that addition has no carries, and that use each digit value the same number of times. Their bound is $r_3(N) \geq N^{1 - c/\log\log N}$ for a constant $c > 0$. So $r_3(N) \geq N^{1 - \delta}$ for every $\delta > 0$ and all large $N$. Behrend replaced the condition on the digit counts by a condition on the sum of the squares of the digits, and this gave a much better bound with a shorter proof.

### Behrend's construction

The idea of Behrend is geometric. A sphere in $\mathbb{R}^n$ contains no three distinct collinear points, so the lattice points on a sphere form a 3AP-free set in $\mathbb{Z}^n$. Many lattice points of a box lie on one sphere, by the pigeonhole principle. The map that reads a vector as the digits of an integer, in a base large enough to prevent carries, sends this set into $\mathbb{N}$ and keeps the property.

**Lemma (Spheres are strictly convex).** Let $u, v, w \in \mathbb{R}^n$ have $\lVert u \rVert = \lVert v \rVert = \lVert w \rVert$, and let $u + w = 2v$. Then $u = v = w$.

*Proof.* Let $R = \lVert u \rVert$. The parallelogram law gives $\lVert u + w \rVert^2 + \lVert u - w \rVert^2 = 2\lVert u \rVert^2 + 2 \lVert w \rVert^2 = 4R^2$. The left side is $\lVert 2v \rVert^2 + \lVert u - w \rVert^2 = 4R^2 + \lVert u - w \rVert^2$. So $\lVert u - w \rVert = 0$, then $u = w$ and $v = (u + w)/2 = u$. $\square$

Mathlib: `Behrend.threeAPFree_sphere` (Mathlib). For $n, d, k \in \mathbb{N}$, Mathlib writes `Behrend.box n d` for the vectors $x \in \mathbb{N}^n$ with $x_i < d$ for all $i$, and `Behrend.sphere n d k` for the $x$ in the box with $\sum_i x_i^2 = k$. The lemma says that `sphere n d k` is 3AP-free as a subset of $\mathbb{N}^n$.

**Lemma (Digits without carries).** Let $n \geq 0$ and $d \geq 1$, and let $\varphi(x) = \sum_{i < n} x_i (2d - 1)^i$ for $x$ in the box $\{0, \dots, d - 1\}^n$. Then $\varphi$ is injective, its values lie in $\{0, \dots, (2d - 1)^n - 1\}$, and for $x, y, z$ in the box, $\varphi(x) + \varphi(z) = 2\varphi(y)$ holds if and only if $x + z = 2y$.

Mathlib: `Behrend.map_injOn` (Mathlib) and `Behrend.map_le_of_mem_box` (Mathlib). The first gives the injectivity and the second gives the bound on the values. The equivalence is a step in the proof of `Behrend.threeAPFree_image_sphere` (Mathlib).

*Proof.* The integers $x_i$, $x_i + z_i$ and $2 y_i$ lie in $\{0, \dots, 2d - 2\}$. So $\varphi(x)$, $\varphi(x) + \varphi(z) = \sum (x_i + z_i)(2d-1)^i$ and $2\varphi(y) = \sum 2 y_i (2d-1)^i$ are expansions in base $2d - 1$ with digits below the base. The uniqueness of such expansions gives the injectivity and the equivalence. The largest value is $\sum_{i<n} (d - 1)(2d - 1)^i < (2d - 1)^n$. $\square$

**Theorem (Behrend, finite form).** For all $n, d \in \mathbb{N}$,
$$r_3\bigl((2d - 1)^n\bigr) \geq \frac{d^n}{n d^2},$$
where the right side is read as $0$ when $n d = 0$.

Mathlib: `Behrend.exists_large_sphere` (Mathlib), `Behrend.card_sphere_le_rothNumberNat` (Mathlib) and `Behrend.bound_aux'` (Mathlib). The first says that for all $n, d$ some $k$ has $d^n/(n d^2) \leq \# \operatorname{sphere}(n, d, k)$ in $\mathbb{R}$. The second says that $\# \operatorname{sphere}(n, d, k) \leq r_3((2d - 1)^n)$. The third is the theorem.

*Proof.* If $n = 0$ or $d = 0$ the right side is $0$. Let $n, d \geq 1$. The box has $d^n$ points, and the sum of squares $\sum x_i^2$ of a point lies in $\{0, 1, \dots, n(d - 1)^2\}$, a set of $n(d - 1)^2 + 1$ values. By the pigeonhole principle some value $k$ is taken by at least $d^n/(n(d-1)^2 + 1)$ points. Since $n d^2 - n(d - 1)^2 = n(2d - 1) \geq 1$, this is at least $d^n/(n d^2)$. The sphere for $k$ is 3AP-free by the first lemma. By the second lemma its image under $\varphi$ is a 3AP-free subset of $\{0, \dots, (2d - 1)^n - 1\}$ of the same size. $\square$

**Remark (Formalization).** The Mathlib statement is an inequality in $\mathbb{R}$ with the quotient $(d^n : \mathbb{R}) / (n d^2 : \mathbb{R})$. For $n = 0$ or $d = 0$ the divisor is $0$, and Mathlib's convention $x/0 = 0$ makes the quotient $0$. So the statement holds with no hypothesis on $n$ and $d$, and it says nothing in these cases. The source uses the same convention in its own form (Section 3), where it requires $0 < n$ only through the later count.

The choice of $n$ and $d$ gives the asymptotic bound.

**Corollary (Behrend).** As $N \to \infty$,
$$r_3(N) \geq N \exp\Bigl(-\bigl(2\sqrt{2 \log 2} + o(1)\bigr)\sqrt{\log N}\Bigr).$$

Not in the source. The source keeps the number $n$ of digits fixed and needs only a density $N^{-\delta}$, [Behrend's sets](/decl/New.exists_three_term_free/).

*Proof.* Let $N \geq 3$ and $n \geq 3$, put $M = N^{1/n}$, and let $d = \lfloor (M + 1)/2 \rfloor$. Suppose $M \geq 3$, so that $d \geq 1$. Then $2d - 1 \leq M$, so $(2d - 1)^n \leq N$, and $d \geq (M - 1)/2$. The theorem and the monotonicity of $r_3$ give
$$r_3(N) \geq \frac{d^{n - 2}}{n} \geq \frac{1}{n} \Bigl(\frac{M - 1}{2}\Bigr)^{n - 2} = \frac{4}{n}\, \frac{N}{M^2\, 2^n} \Bigl(1 - \frac1M\Bigr)^{n-2}.$$
Now take $n = \lceil \sqrt{2 \log N / \log 2}\, \rceil$. Then $\log M = \log N/n = \sqrt{(\log 2/2) \log N} + O(1)$ and $n \log 2 = \sqrt{2 \log 2 \cdot \log N} + O(1)$. So
$$\log\bigl(M^2 2^n\bigr) = 2\sqrt{\tfrac{\log 2}{2}\log N} + \sqrt{2 \log 2 \log N} + O(1) = 2\sqrt{2 \log 2}\,\sqrt{\log N} + O(1).$$
Since $M$ grows faster than every power of $n$, the factor $(1 - 1/M)^{n - 2}$ tends to $1$, and $\log(4/n) = O(\log\log N)$. Both are $o(\sqrt{\log N})$ in the exponent. $\square$

The constant is $2\sqrt{2\log 2} = 2.354\ldots$. Mathlib proves a version with the constant $4$ and no error term.

**Theorem (Behrend, Mathlib form).** For every $N \in \mathbb{N}$, $N \exp(-4\sqrt{\log N}) \leq r_3(N)$, and the inequality is strict for $N \geq 4096$.

Mathlib: `Behrend.roth_lower_bound` (Mathlib) and `Behrend.roth_lower_bound_explicit` (Mathlib).

**Remark (Formalization).** For $N = 0$ the real logarithm of Mathlib has $\log 0 = 0$, and both sides are $0$. For $1 \leq N < 4096$ Mathlib shows that the left side is at most $1$, and $r_3(N) \geq r_3(1) = 1$. The source uses neither of these two theorems. It needs a form with weights and a modulus and with an explicit count, so it uses only `Behrend.exists_large_sphere` and proves the rest itself (Section 3).

The density of Behrend's set in $[0, N)$ is $\exp(-c\sqrt{\log N})$. This is smaller than every fixed power of $\log N$ but larger than $N^{-\delta}$ for every fixed $\delta > 0$. For the argument the density $N^{-\delta}$ is enough (Section 1). So the full strength of Behrend's bound is not needed, and the source works with a fixed number $n$ of digits. With $d \approx N^{1/n}$ the theorem gives the density $\gg 2^{-n} N^{-2/n}/n$, a fixed power of $N$ with a small exponent.

Behrend's bound stood for more than sixty years. Elkin gained a factor $(\log N)^{1/4}$: he showed $r_3(N) \gg N (\log N)^{1/4} 2^{-2\sqrt{2 \log_2 N}}$. Here $2^{2\sqrt{2\log_2 N}} = \exp(2\sqrt{2\log 2}\sqrt{\log N})$, so the constant in the exponent is still Behrend's. Green and Wolf gave a short proof of Elkin's bound.

### Upper bounds: the theorem of Roth

**Theorem (Roth).** There is a constant $C$ such that $r_3(N) \leq C N/\log\log N$ for all $N \geq 3$. In particular $r_3(N) = o(N)$.

The proof is by a *density increment*. Let $A \subseteq \{0, \dots, N - 1\}$ have density $\alpha$ and no nontrivial three-term progressions. The number of solutions of $a + c = 2b$ in $A$ is a sum over the frequencies $\theta$ of $\hat 1_A(\theta)^2 \hat 1_A(-2\theta)$. A random set of density $\alpha$ has about $\alpha^3 N^2$ solutions, and $A$ has only the $\# A$ trivial ones. So for $N$ large in terms of $\alpha$ one Fourier coefficient at a nonzero frequency is large, of size $\gg \alpha^2 N$. Dirichlet's approximation theorem splits $[0, N)$ into long progressions on which this frequency is almost constant, and on one of them $A$ has density at least $\alpha + c\alpha^2$. The new progression has length about $\sqrt{N}$, and $A$ is again 3AP-free in it. After about $1/\alpha$ steps the density would exceed $1$, so $N$ cannot be large in terms of $\alpha$. The bookkeeping gives $\alpha \ll 1/\log\log N$. Tao and Vu give a complete account in Chapter 10 of *Additive Combinatorics*.

Mathlib: `rothNumberNat_isLittleO_id` (Mathlib) and `roth_3ap_theorem_nat` (Mathlib). The first says that $r_3(N) = o(N)$ as $N \to \infty$. The second says: for $\varepsilon > 0$ and $n$ at least a bound $\operatorname{cornersTheoremBound}(\varepsilon/3)$ that depends only on $\varepsilon$, a subset of $\{0, \dots, n - 1\}$ with at least $\varepsilon n$ elements is not 3AP-free. Mathlib does not prove Roth's rate. It deduces the qualitative statement from the corners theorem, which it proves through the triangle removal lemma.

The upper bound has been improved many times:

- Heath-Brown and Szemerédi, independently: $r_3(N) \ll N/(\log N)^c$ for a constant $c > 0$.
- Bourgain: $r_3(N) \ll N (\log\log N/\log N)^{1/2}$.
- Sanders: $r_3(N) \ll N/(\log N)^{1 - o(1)}$.
- Kelley and Meka: $r_3(N) \leq N \exp(-c(\log N)^{1/12})$ for a constant $c > 0$.
- Bloom and Sisask: the same with the exponent $1/9$ in place of $1/12$.

So $\log(N/r_3(N))$ lies between a constant times $(\log N)^{1/9}$ and a constant times $(\log N)^{1/2}$. For the argument the upper bounds have one message: a set of exponents of positive density cannot work, and any construction must give up a factor that grows with $N$. The factor that the argument can afford is $\log b \approx N^{\varepsilon/11}$, a power of $N$. The digit sets of Erdős and Turán lose the fixed power $N^{0.369\ldots}$, which is too much when $\varepsilon$ is small. Behrend's construction loses less than every power. So the difficulty is not the size alone. It is the size together with the weights and the modulus.

### Weights and a modulus

The argument needs more than 3AP-free sets. It needs a set $S$ of integers with no solutions of
$$(\alpha + \alpha')\, e_2 = \alpha e_1 + \alpha' e_3, \qquad e_1, e_2, e_3 \in S \text{ not all equal},$$
for all positive integers $\alpha, \alpha'$ with $\alpha + \alpha' \leq L$ at once, and with the equation read modulo an integer $o$. The progressions are the case $\alpha = \alpha' = 1$. An equation $\sum_i a_i x_i = 0$ with $\sum_i a_i = 0$ is called *invariant*: its solution set contains the trivial solutions $x_1 = \dots = x_k$, and it does not change under translation and dilation. Ruzsa developed the general theory of the extremal sizes for invariant equations. Shapira gave constructions of Behrend's type that avoid several equations at once. The docstring of the source file `New/Reduction/Data/Existence.lean` names Shapira's paper and Behrend's paper as the sources of its construction.

Behrend's two lemmas extend at once to the weighted equation.

- Strict convexity holds with weights. If $\lVert u \rVert = \lVert v \rVert = \lVert w \rVert$ and $(\alpha + \alpha') v = \alpha u + \alpha' w$ with $\alpha, \alpha' > 0$, then $u = v = w$. Indeed $(\alpha + \alpha')(\alpha \lVert u \rVert^2 + \alpha' \lVert w \rVert^2) - \lVert \alpha u + \alpha' w \rVert^2 = \alpha \alpha' \lVert u - w \rVert^2$, and the left side is $(\alpha + \alpha')^2 R^2 - (\alpha + \alpha')^2 R^2 = 0$.
- The digits need a larger base. For coordinates below $H$ and $\alpha + \alpha' \leq L$, the coordinates of $\alpha u + \alpha' w$ and of $(\alpha + \alpha') v$ are below $L H$. So the base $L H$ prevents carries for all the equations at once.

A modulus costs nothing more. If all the integers $\alpha e_1 + \alpha' e_3$ and $(\alpha + \alpha') e_2$ lie in $[0, o)$, a congruence modulo $o$ between two of them is an equality. With $n$ digits in base $L H$ this holds when $(L H)^n \leq o$.

The price of the weights is the base. The sphere has about $H^{n-2}/n$ points, and the set lies in $[0, (LH)^n)$. So the density is about $L^{-n} H^{-2}/n$. In the argument $N = 2^s$ and $L = 2 l_0 \leq 162 s$, so $L$ is at most a constant times $\log N$, and the factor $L^{-n}$ is a power of $\log N$ for fixed $n$. Section 3 states and proves this form, and Section 4 shows that the loss is absorbed.

**Example (A sphere in base 6).** Take $n = 2$, $H = 3$ and $L = 2$, so that only the progressions $\alpha = \alpha' = 1$ are excluded and the base is $L H = 6$. The box $\{0, 1, 2\}^2$ has nine points, with the sums of squares $0, 1, 1, 2, 4, 4, 5, 5, 8$. The sphere $k = 5$ is $\{(1, 2), (2, 1)\}$, and its image under $(v_0, v_1) \mapsto v_0 + 6 v_1$ is $\{13, 8\}$. Two points are always 3AP-free. Larger examples need a larger box. Volume 1 works out the case $n = 3$ in base $6$, where one sphere gives the set $\{8, 13, 38, 48, 73, 78\}$, in [the data exist](/chapter/data-exist/).
