---
title: The form of the source
lean:
  - New/Reduction/Data/Existence.lean
decls:
  - New.eq_of_add_mul_eq_of_sum_sq_eq
  - New.exists_three_term_free
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The form of the source

The source proves one combinatorial theorem about sets without progressions. It is Behrend's construction with three changes: it avoids all the weighted equations $(\alpha + \alpha') e_2 = \alpha e_1 + \alpha' e_3$ with $\alpha + \alpha' \leq L$ at once, it reads them modulo an integer $o$, and it keeps the number $n$ of digits as a free parameter with an explicit count. This section states the theorem exactly as Lean states it and gives its proof. Volume 1 states the same results in [the data exist](/chapter/data-exist/). Here the emphasis is on the comparison with the classical form of Section 2 and on the role of each hypothesis.

### Strict convexity with weights

**Lemma (Strict convexity with weights).** Let $\iota$ be a finite type, let $\alpha, \alpha' \in \mathbb{N}$ with $0 < \alpha$ and $0 < \alpha'$, and let $u, v, w \colon \iota \to \mathbb{N}$. Suppose that $(\alpha + \alpha') v_l = \alpha u_l + \alpha' w_l$ in $\mathbb{Z}$ for every $l \in \iota$, that $\sum_l u_l^2 = \sum_l v_l^2$, and that $\sum_l v_l^2 = \sum_l w_l^2$. Then $u = v$ and $v = w$.

Lean: `New.eq_of_add_mul_eq_of_sum_sq_eq` (New/Reduction/Data/Existence.lean).

*Proof.* For each $l$, the identity
$$(\alpha + \alpha')\bigl(\alpha u_l^2 + \alpha' w_l^2\bigr) - \bigl((\alpha + \alpha') v_l\bigr)^2 = (\alpha + \alpha')\bigl(\alpha u_l^2 + \alpha' w_l^2\bigr) - (\alpha u_l + \alpha' w_l)^2 = \alpha\alpha' (u_l - w_l)^2$$
holds in $\mathbb{Z}$. Sum over $l$ and put $R = \sum_l u_l^2 = \sum_l v_l^2 = \sum_l w_l^2$. The left side becomes $(\alpha + \alpha')(\alpha + \alpha') R - (\alpha + \alpha')^2 R = 0$. So $\alpha \alpha' \sum_l (u_l - w_l)^2 = 0$. Since $\alpha\alpha' > 0$, every $u_l - w_l$ is $0$, and $u = w$. Then $(\alpha + \alpha') v_l = (\alpha + \alpha') u_l$, and $v = u$ because $\alpha + \alpha' > 0$. $\square$

The proof in Lean follows these lines: it proves the summed identity by `ring` after it rewrites the three sums of squares, and it cancels the positive factors at the end. The vectors have entries in $\mathbb{N}$ and the hypothesis on the coordinates is read in $\mathbb{Z}$. This is only a matter of where the subtraction $u_l - w_l$ takes place.

### The count on a sphere

The source takes the count of points on a sphere from Mathlib.

**Lemma (A large sphere).** For all $n, d \in \mathbb{N}$ there is $k \in \mathbb{N}$ with
$$\frac{d^n}{n d^2} \leq \#\bigl\{ x \in \{0, \dots, d - 1\}^n : \textstyle\sum_i x_i^2 = k \bigr\}$$
in $\mathbb{R}$.

Mathlib: `Behrend.exists_large_sphere` (Mathlib).

The proof is the pigeonhole argument of Section 2: the $d^n$ points of the box have at most $n(d - 1)^2 + 1 \leq n d^2$ sums of squares. The quotient is a quotient in $\mathbb{R}$, so for $n = 0$ or $d = 0$ the left side is $0$ and the lemma says nothing.

### Behrend's construction with weights and a modulus

**Theorem (Behrend's construction with weights and a modulus).** Let $n, H, L, o \in \mathbb{N}$ with $0 < L$ and $(L H)^n \leq o$. There is a finite set $S \subseteq \mathbb{N}$ with the three properties:

1. every $e \in S$ has $e < o$;
2. $H^n / (n H^2) \leq \# S$ in $\mathbb{R}$;
3. for all $e_1, e_2, e_3 \in S$ and all $\alpha, \alpha' \in \mathbb{N}$ with $0 < \alpha$, $0 < \alpha'$ and $\alpha + \alpha' \leq L$,
$$(\alpha + \alpha')\, e_2 \equiv \alpha e_1 + \alpha' e_3 \pmod{o} \quad\Longrightarrow\quad e_1 = e_2 \text{ and } e_2 = e_3.$$

Lean: `New.exists_three_term_free` (New/Reduction/Data/Existence.lean).

*Proof.* By the lemma on a large sphere choose $k$ with $H^n/(nH^2) \leq \# \Sigma$, where $\Sigma$ is the set of $v \in \{0, \dots, H - 1\}^n$ with $\sum_l v_l^2 = k$. Let $B = L H$ and let $\varphi(v) = \sum_{l < n} v_l B^l$ be the number with digits $v$ in base $B$. Put $S = \varphi(\Sigma)$.

*Property 1.* A vector $v$ with all $v_l < B$ has $\varphi(v) < B^n \leq o$, by the uniqueness of expansions in base $B$. Every $v \in \Sigma$ has $v_l < H \leq L H = B$, since $L \geq 1$.

*Property 2.* The map $\varphi$ is injective on the vectors with entries below $B$ (`Behrend.map_injOn` (Mathlib)), so $\# S = \# \Sigma \geq H^n/(nH^2)$.

*Property 3.* Let $u, v, w \in \Sigma$ with $\varphi(u) = e_1$, $\varphi(v) = e_2$, $\varphi(w) = e_3$, and let the congruence hold. The map $\varphi$ is additive, so $(\alpha + \alpha') e_2 = \varphi((\alpha + \alpha') v)$ and $\alpha e_1 + \alpha' e_3 = \varphi(\alpha u + \alpha' w)$. The entries of the two vectors are below $(\alpha + \alpha') H \leq L H = B$. So both integers lie in $[0, B^n) \subseteq [0, o)$, and a congruence modulo $o$ between two integers in $[0, o)$ is an equality. By the injectivity of $\varphi$ on vectors with entries below $B$, we get $(\alpha + \alpha') v = \alpha u + \alpha' w$ as vectors. All three vectors lie on the sphere of radius $\sqrt{k}$, so strict convexity with weights gives $u = v = w$, and so $e_1 = e_2 = e_3$. $\square$

Each hypothesis has one role. The bound $\alpha + \alpha' \leq L$ and the base $L H$ prevent carries in the weighted sums. The room $(L H)^n \leq o$ turns the congruence into an equality. The positivity of $L$ makes the digits of the sphere lie below the base.

**Example (Carries break the construction).** Take $n = 3$, $H = 4$ and the sphere $k = 10$. Its points are the six permutations of $(0, 1, 3)$. In base $8$, which is enough for the progressions with $\alpha = \alpha' = 1$, the set is $\{11, 25, 67, 88, 193, 200\}$. It has no nontrivial three-term progression. But with $\alpha = 1$ and $\alpha' = 2$,
$$3 \cdot 67 = 201 = 25 + 2 \cdot 88.$$
The digit vectors are $25 \leftrightarrow (1, 3, 0)$, $67 \leftrightarrow (3, 0, 1)$ and $88 \leftrightarrow (0, 3, 1)$. Here $3 \cdot (3, 0, 1) = (9, 0, 3)$ and $(1, 3, 0) + 2 \cdot (0, 3, 1) = (1, 9, 2)$. These vectors differ, but both have entries up to $9 \geq 8$, and the carries make $9 + 3 \cdot 64 = 1 + 9 \cdot 8 + 2 \cdot 64 = 201$. With the base $L H = 12$ for $L = 3$ the same sphere gives the set $\{15, 37, 147, 180, 433, 444\}$. Now the weighted sums have no carries, and the theorem shows that this set has no solution for $\alpha + \alpha' \leq 3$ except $e_1 = e_2 = e_3$.

### Comparison with the classical form

**Remark (Formalization).** Behrend's theorem in its classical form, Section 2, is about the single equation $e_1 + e_3 = 2 e_2$ in the integers. The source proves a form for all the weights $\alpha, \alpha' > 0$ with $\alpha + \alpha' \leq L$ at once and for congruences modulo $o$. This is the kind of statement that Shapira's paper considers, several equations at once, and the docstring of the file names that paper. For $L = 2$ and $o \geq (2H)^n$ the theorem contains the case of three-term progressions, in the base $2H$ in place of Behrend's $2H - 1$. The argument needs the weighted form: Section 4 turns the configuration of sparseness into the equation with $\alpha = 2(j - i)$ and $\alpha' = 2i$, and $j$ runs up to $l_0$. It also needs the congruence, since the exponents of a group element of order $2^s$ are only defined modulo $2^s$.

**Remark (Formalization).** The count $H^n/(nH^2)$ is a quotient in $\mathbb{R}$. With Lean's convention $x/0 = 0$ it is $0$ when $n = 0$ or $H = 0$. In these cases property 2 is empty and the set $S$ may be empty. So the theorem needs no hypothesis $0 < n$ or $0 < H$. The later lemma [`New.Parameters.exists_isSparse`](/decl/New.Parameters.exists_isSparse/) assumes $0 < n$, and there the count is real.

**Remark (Formalization).** The conclusion is $e_1 = e_2 \wedge e_2 = e_3$, for all $e_1, e_2, e_3 \in S$, distinct or not. It also excludes the degenerate triples. For instance $e_1 = e_3 \neq e_2$ would give $(\alpha + \alpha')(e_2 - e_1) \equiv 0 \pmod o$, and the theorem says that this cannot happen inside $S$. Section 4 uses the conclusion in this form: it does not know in advance that the three places of a configuration are distinct.

**Remark (Formalization).** The number $n$ of digits is a free parameter. Behrend's optimal choice $n \approx \sqrt{2\log N/\log 2}$ is not used. In the argument $n$ is fixed once $\varepsilon$, $q_0$ and $d$ are fixed (Section 4), and the theorem is applied with $H$ a power of $2$ near $(2^s/W)^{1/n}$. So the source proves less than Behrend's asymptotic bound. It proves the finite statement that the argument needs, with explicit constants.

### The density of the set

The set $S$ lies in $[0, (LH)^n)$ and has at least $H^{n - 2}/n$ elements. Its density in that interval is at least
$$\frac{H^{n-2}/n}{(LH)^n} = \frac{1}{n L^n H^2}.$$
Two factors are lost: $L^n$ from the base and $n H^2$ from the pigeonhole step. In the application $L = 2 l_0 \leq 162 s$, so $L^n$ is a fixed power of $s \approx \log 2^s$. The factor $H^2$ is $(LH)^{2}/L^2$, and $(L H)^n$ is about the order $2^s$ of the group. So $H^2 \approx 2^{2s/n}/L^2$, a small power of the group order when $n$ is large. Section 4 makes these estimates exact with the scale $W$: there $W$ absorbs $L^n$, the factor $3 l_0 n 2^n$ and $H^2$, and the final loss is $W^6$.

**Example (The sizes in the argument).** In the data at a large integer $x$, $2^s = m^{22}$ with $m \approx \sqrt{x}$, so $2^s \approx x^{11}$ and $s \approx 11 \log_2 x$. The weights run up to $L = 2 l_0 \leq 162 s$, a constant times $\log x$. The scale is $W = x^{\varepsilon/6}$, and $n$ is a fixed integer with $99 q_0 d < n\varepsilon/6$. The cube side $H$ is a power of $2$ with $H^n \leq 2^s/W < (2H)^n$. So $H \approx x^{11/n}$, and the density $1/(nL^nH^2)$ is about $x^{-22/n}$ up to powers of $\log x$. Since $n > 594\, q_0 d/\varepsilon$ is huge, this is far better than the density $x^{-\varepsilon}$ that the argument needs.
