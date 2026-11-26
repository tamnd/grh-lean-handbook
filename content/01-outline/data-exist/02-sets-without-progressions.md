---
title: Sets without progressions
lean:
  - New/Reduction/Data/Existence.lean
decls:
  - New.eq_of_add_mul_eq_of_sum_sq_eq
  - New.exists_three_term_free
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Sets without progressions

This section proves Behrend's construction of large sets without three-term progressions. The source needs it in a form with weights: the congruence $(\alpha + \alpha') e_2 \equiv \alpha e_1 + \alpha' e_3$ modulo an integer $o$ must force $e_1 = e_2 = e_3$ for all positive weights $\alpha$, $\alpha'$ up to a bound. Section 3 applies the result to exponents of a root of unity, and so builds the set $\Phi_b$ of places.

### The problem

Let $r_3(N)$ be the largest size of a set $S \subseteq \{0, 1, \dots, N - 1\}$ that contains no progression $e_1, e_2, e_3$ with $e_1 < e_2 < e_3$ and $2 e_2 = e_1 + e_3$. Roth's theorem says $r_3(N) = o(N)$. In the other direction, Behrend proved
$$r_3(N) \geq N \exp\bigl(-(c + o(1))\sqrt{\log N}\bigr), \qquad c = 2\sqrt{2 \log 2}.$$
The source does not need the exact form of this bound. It needs three features of Behrend's method:

1. the set has an explicit size, a fixed power of the side of a cube divided by a polynomial;
2. the method works for all equations $(\alpha + \alpha') e_2 = \alpha e_1 + \alpha' e_3$ with bounded positive weights at once;
3. the method works modulo $o$, if $o$ is large against the digits.

The idea is geometric. A sphere in $\mathbb{R}^n$ is strictly convex, so it contains no three distinct collinear points with one between the other two. Integer points of a sphere in a box therefore have no nontrivial solutions of $(\alpha + \alpha') v = \alpha u + \alpha' w$. Some sphere carries many integer points of the box, by pigeonhole. Read each point as the digit vector of an integer in a large base. If the base is large against the weights, there are no carries, and an equation between integers becomes an equation between digit vectors.

### Strict convexity

**Lemma (Strict convexity of a sphere).** Let $\iota$ be a finite set, let $\alpha, \alpha'$ be positive integers, and let $u, v, w \colon \iota \to \mathbb{N}$. Assume that $(\alpha + \alpha') v_l = \alpha u_l + \alpha' w_l$ for every $l \in \iota$, and that $\sum_l u_l^2 = \sum_l v_l^2 = \sum_l w_l^2$. Then $u = v$ and $v = w$.
Lean: `New.eq_of_add_mul_eq_of_sum_sq_eq` (New/Reduction/Data/Existence.lean).

*Proof.* For each coordinate $l$, expand and use $(\alpha + \alpha') v_l = \alpha u_l + \alpha' w_l$:
$$(\alpha + \alpha')(\alpha u_l^2 + \alpha' w_l^2) - ((\alpha + \alpha') v_l)^2 = \alpha^2 u_l^2 + \alpha\alpha'(u_l^2 + w_l^2) + \alpha'^2 w_l^2 - (\alpha u_l + \alpha' w_l)^2 = \alpha\alpha'(u_l - w_l)^2.$$
Let $k$ be the common value of the three sums of squares. Add the identity over $l$:
$$\sum_l \alpha\alpha'(u_l - w_l)^2 = (\alpha + \alpha')(\alpha k + \alpha' k) - (\alpha + \alpha')^2 k = 0.$$
Each term on the left is at least $0$, and $\alpha\alpha' > 0$. So $u_l = w_l$ for every $l$. Then $(\alpha + \alpha') v_l = (\alpha + \alpha') u_l$, so $v_l = u_l$. $\square$

The lemma is the quantitative form of strict convexity: the defect $\alpha\alpha' |u - w|^2$ is the amount by which the weighted mean of two points of the sphere lies inside the sphere.

### A sphere with many points

Let $n, H \geq 0$ be integers. The *box* is $\{0, 1, \dots, H - 1\}^n$, and the *sphere* of radius $\sqrt{k}$ in it is
$$\Sigma(n, H, k) = \Bigl\{ v \in \{0, \dots, H - 1\}^n : \sum_{l} v_l^2 = k \Bigr\}.$$

**Lemma (A large sphere).** For all $n, H \in \mathbb{N}$ there is a $k \in \mathbb{N}$ with
$$\frac{H^n}{n H^2} \leq \#\Sigma(n, H, k),$$
where the left side is a real number and $x/0 = 0$.
Lean: `Behrend.exists_large_sphere` (Mathlib).

*Proof.* If $n = 0$ or $H = 0$, the left side is $0$ by the convention $x/0 = 0$, and any $k$ works. Let $n, H \geq 1$. The box has $H^n$ points. For each point, $\sum_l v_l^2$ is an integer in $[0, n(H - 1)^2]$, so it takes at most $n(H - 1)^2 + 1$ values. By pigeonhole one value $k$ is taken by at least $H^n / (n(H - 1)^2 + 1)$ points. Finally $n H^2 - n(H - 1)^2 = n(2H - 1) \geq 1$, so $n(H - 1)^2 + 1 \leq n H^2$. $\square$

### Behrend's construction

For a base $B \geq 1$ the digit map is
$$\operatorname{map}_B(v) = \sum_{l = 0}^{n - 1} v_l B^l, \qquad v \in \mathbb{N}^n.$$
It is additive, and it is injective on vectors whose entries are less than $B$, by uniqueness of the expansion in base $B$. On such vectors its values are less than $B^n$.

**Theorem (Behrend's sets with weights).** Let $n, H, L, o$ be natural numbers with $0 < L$ and $(LH)^n \leq o$. There is a finite set $S \subseteq \mathbb{N}$ with the following three properties.

1. Every $e \in S$ satisfies $e < o$.
2. $H^n / (n H^2) \leq \#S$, as real numbers, with $x/0 = 0$.
3. Let $e_1, e_2, e_3 \in S$, and let $\alpha, \alpha'$ be natural numbers with $0 < \alpha$, $0 < \alpha'$ and $\alpha + \alpha' \leq L$. If $(\alpha + \alpha') e_2 \equiv \alpha e_1 + \alpha' e_3 \pmod{o}$, then $e_1 = e_2$ and $e_2 = e_3$.

Lean: `New.exists_three_term_free` (New/Reduction/Data/Existence.lean).

*Proof.* Put $B = LH$. Take $k$ from [the lemma on a large sphere](/decl/Behrend.exists_large_sphere/), and put $S = \operatorname{map}_B(\Sigma(n, H, k))$.

*Property 1.* A vector $v$ of the sphere has entries $v_l \leq H - 1 < H \leq LH = B$, since $L \geq 1$. So $\operatorname{map}_B(v) < B^n \leq o$.

*Property 2.* The map $\operatorname{map}_B$ is injective on vectors with entries below $B$, and the sphere consists of such vectors. So $\#S = \#\Sigma(n, H, k) \geq H^n/(nH^2)$.

*Property 3.* Write $e_1 = \operatorname{map}_B(u)$, $e_2 = \operatorname{map}_B(v)$ and $e_3 = \operatorname{map}_B(w)$ with $u, v, w$ on the sphere. By additivity,
$$(\alpha + \alpha') e_2 = \operatorname{map}_B((\alpha + \alpha') v), \qquad \alpha e_1 + \alpha' e_3 = \operatorname{map}_B(\alpha u + \alpha' w).$$
The entries of both vectors are less than $B$. Indeed $(\alpha + \alpha') v_l \leq L(H - 1) < LH$, and $\alpha u_l + \alpha' w_l \leq (\alpha + \alpha')(H - 1) < LH$. So both integers are less than $B^n \leq o$. Two integers in $[0, o)$ that are congruent modulo $o$ are equal. So $\operatorname{map}_B((\alpha + \alpha')v) = \operatorname{map}_B(\alpha u + \alpha' w)$, and injectivity on vectors with entries below $B$ gives $(\alpha + \alpha') v = \alpha u + \alpha' w$. The three vectors have the same sum of squares $k$. [The lemma on strict convexity](/decl/New.eq_of_add_mul_eq_of_sum_sq_eq/) gives $u = v = w$, hence $e_1 = e_2 = e_3$. $\square$

The proof has two inputs: no carries, and strict convexity. The first is the reason for the factor $L$ in the base. The congruence modulo $o$ costs nothing, because both sides already lie in $[0, o)$.

### A small case

**Example (Three digits in base 6).** Take $n = 3$, $H = 3$ and $L = 2$, so that the only weights are $\alpha = \alpha' = 1$ and the congruence is $2 e_2 \equiv e_1 + e_3$. Take $o = (LH)^n = 216$. The box $\{0, 1, 2\}^3$ has $27$ points. The sums of squares and the number of points on each sphere are:

| $k$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 8 | 9 | 12 |
|---|---|---|---|---|---|---|---|---|---|---|
| points | 1 | 3 | 3 | 1 | 3 | 6 | 3 | 3 | 3 | 1 |

The largest sphere is $k = 5$. Its points are the six permutations of $(0, 1, 2)$. In base $6$ they give
$$S = \{8, 13, 38, 48, 73, 78\},$$
for example $(2, 1, 0) \mapsto 2 + 1 \cdot 6 + 0 \cdot 36 = 8$ and $(0, 1, 2) \mapsto 0 + 6 + 72 = 78$. The bound of the theorem is $H^n/(nH^2) = 27/27 = 1$, and the set has $6$ elements. The three pairs $\{8, 78\}$, $\{13, 73\}$ and $\{38, 48\}$ all have the sum $86$. Their common midpoint is $43 = \operatorname{map}_6(1, 1, 1)$, and $(1, 1, 1)$ lies on the sphere $k = 3$, not on $k = 5$. So none of the three pairs is completed to a progression by an element of $S$. This is the geometry of the lemma: the midpoint of two points of a sphere lies strictly inside it. A check of the other pairs shows that $S$ has no progression of length three, even modulo $216$, because all sums $e_1 + e_3$ and all doubles $2e_2$ are less than $216$.

### Behrend's bound

The classical bound follows from the theorem with $L = 2$ and a good choice of $n$ and $H$. It is not in the source, and it is not used. It shows how much the explicit count gives.

**Example (Behrend's lower bound for $r_3$).** Let $N$ be large. Take $L = 2$, an integer $n \geq 1$, and $H = \lfloor N^{1/n}/2 \rfloor$, so that $(2H)^n \leq N$. The theorem with $o = N$ gives a set $S \subseteq [0, N)$ without three-term progressions: an integer progression $2e_2 = e_1 + e_3$ is in particular a congruence modulo $N$. Its size is at least
$$\frac{H^n}{n H^2} \geq \frac{(N^{1/n}/2 - 1)^n}{n N^{2/n}/4}.$$
For $n \approx \sqrt{2 \log N / \log 2}$, the term $N^{1/n}$ tends to infinity, and $(N^{1/n}/2 - 1)^n = (N^{1/n}/2)^n e^{O(n N^{-1/n})} = N 2^{-n} e^{o(\sqrt{\log N})}$. The logarithm of the bound is then
$$\log N - n \log 2 - \frac{2 \log N}{n} + o\bigl(\sqrt{\log N}\bigr) = \log N - 2\sqrt{2 \log 2}\,\sqrt{\log N} + o\bigl(\sqrt{\log N}\bigr),$$
since $n \log 2 + 2\log N / n$ is least, with the value $2\sqrt{2 \log 2 \log N}$, at $n = \sqrt{2 \log N/\log 2}$. This is Behrend's bound $r_3(N) \geq N \exp(-(2\sqrt{2\log 2} + o(1))\sqrt{\log N})$.

The source uses a much cruder choice. In Section 3 the number of digits $n$ is fixed, $H$ is a power of $2$, and the loss $nH^2$ is paid with a power of the scale $W$. The source needs a set of density at least $W^{-6}$ in a group of order about $x^{11}$, where $W = x^{\varepsilon/6}$. Behrend's density $\exp(-c\sqrt{\log N})$ would be far more than enough. A fixed number of digits gives the density $H^{-2}/n$, which is a power of $W$ and is exactly what the count needs.

### The form in the source

The textbook form is the case $L = 2$ in the integers. The source form differs in three ways, and each one serves Section 3.

**Remark (Formalization).** First, the weights. Section 3 meets the congruence $(2a + 2i) e_2 \equiv 2a e_1 + 2i e_3$ with $a, i > 0$ and $2a + 2i < 2l_0$, so the source allows all weights with $\alpha + \alpha' \leq L$ and takes $L = 2l_0$. Second, the modulus. The exponents $e$ are exponents of an element of order $2^s$ in a group, so the congruence is modulo $o = 2^s$, not an equation in $\mathbb{Z}$. Third, the size. The bound $H^n/(nH^2)$ is the real quotient of two natural numbers. If $n = 0$ or $H = 0$, the denominator is $0$, and the convention $x/0 = 0$ makes the bound $0$, which is true and empty. In the application $n \geq 1$ and $H$ is a power of $2$, so the bound has its intended value. The set $S$ is the image of the sphere of [Mathlib's lemma](/decl/Behrend.exists_large_sphere/), whose radius $k$ is an existential witness: the source does not say which sphere it takes, and the argument does not need to know.

The docstring of the file gives the literature: the construction for several equations at once is due to Shapira (Acta Arith. 2006), after Behrend (Proc. Nat. Acad. Sci. 32, 1946), and a form close to the source's is Lemma 4.1 of Alon and Shapira. The notes at the end of the chapter give the references.
