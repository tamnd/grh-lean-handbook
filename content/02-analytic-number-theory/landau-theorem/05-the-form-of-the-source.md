---
title: The form of the source
lean:
  - Lib/Analytic/Landau.lean
  - Lib/Analytic/EntireLFunction.lean
  - New/Reduction/Zeros/Criterion.lean
decls:
  - New.mem_integrableExpSet_of_summable_taylor
  - New.exists_mul_exp_le
  - New.eventuallyEq_of_eq_far_right
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The form of the source

This section compares the classical theorem of Section 3 with the form that the source proves. Volume 1 states and proves the main lemmas of the source in [Polar pairs and Landau's lemma](/chapter/landau-criterion/#polar-pairs-and-landaus-lemma). This section does not repeat them. It states the three lemmas of the source that Volume 1 uses with no statement of their own, it proves that the classical theorem follows from the form of the source, and it gives a remark on each difference. It ends with a list of what the argument of the source uses.

### The dictionary

The source writes a Laplace transform as a moment generating function, in the language of Mathlib. Let $\mu$ be a measure on $\mathbb{R}$ and let $X : \mathbb{R} \to \mathbb{R}$ be measurable. The set
$$S = \{t \in \mathbb{R} : e^{tX} \text{ is } \mu\text{-integrable}\}$$
is `ProbabilityTheory.integrableExpSet` (Mathlib), and the function $M(s) = \int e^{sX}\, d\mu$ of a complex variable $s$ is `ProbabilityTheory.complexMGF` (Mathlib). If $X \leq 0$ then $S$ is a half-line unbounded to the right, since $e^{tX}$ decreases in $t$. Mathlib proves that $M$ is analytic at each $s$ with $\operatorname{Re} s$ in the interior of $S$, as `ProbabilityTheory.analyticAt_complexMGF` (Mathlib), and that its derivatives there are $M^{(k)}(s) = \int X^k e^{sX}\, d\mu$, as `ProbabilityTheory.iteratedDeriv_complexMGF` (Mathlib).

The classical objects of Section 2 are a special case. Let $\mu$ be a positive Borel measure on $[0, \infty)$, extended by $0$ to $\mathbb{R}$, and let $X(v) = -|v|$. Then $e^{tX(v)} = e^{-tv}$ on the support of $\mu$, so $S$ is the set of $\sigma$ with $F(\sigma) < \infty$, its left end point is $\sigma_c$, and $M(s) = F(s)$ for $\operatorname{Re} s > \sigma_c$. The source uses exactly this choice of $X$, for the measure of [Lemma](/decl/New.exists_measure_laplace_eq/), which has the density $K e^{\beta v} - E(v) e^v$ on $v > 0$.

The chain of the source has six steps. The Taylor step below, the identity theorem below, and the constant below are stated in this section. Landau's lemma [Lemma](/decl/New.exists_Ioi_subset_integrableExpSet_of_analyticAt/), the lemma on a residue of real part at most zero [Lemma](/decl/New.exists_Ioi_subset_integrableExpSet/), and Landau's lemma for polar functions [Theorem](/decl/New.IsPolar.landau/) are stated and proved in Volume 1.

### The Taylor step

**Lemma (The Taylor step).** Let $\mu$ be a measure on $\mathbb{R}$ and let $X$ be measurable with $X(y) \leq 0$ for every $y$. Let $z$ and $\sigma$ be real, with $z$ in the interior of $S$ and $\sigma \leq z$. Let $g : \mathbb{C} \to \mathbb{C}$ be equal to $M$ on a neighbourhood of $z$ in $\mathbb{C}$. Suppose that the series
$$\sum_{k \geq 0} \frac{(\sigma - z)^k}{k!}\, g^{(k)}(z)$$
is summable. Then $\sigma \in S$.

Lean: `New.mem_integrableExpSet_of_summable_taylor` (Lib/Analytic/Landau.lean).

*Proof.* For $k \geq 0$ and $y \in \mathbb{R}$ put $T_k(y) = ((\sigma - z)X(y))^k e^{zX(y)}/k!$. Since $\sigma - z \leq 0$ and $X(y) \leq 0$, the product $(\sigma - z)X(y)$ is $\geq 0$, so $T_k(y) \geq 0$. The exponential series gives $\sum_k T_k(y) = e^{(\sigma - z)X(y)} e^{zX(y)} = e^{\sigma X(y)}$. Since $g = M$ near $z$, we have $g^{(k)}(z) = M^{(k)}(z) = \int X^k e^{zX}\, d\mu$, by the formula of Mathlib, which needs $z$ in the interior of $S$. So the $k$-th term of the series is $\int T_k\, d\mu$, a nonnegative real number. By the theorem of Tonelli for series of nonnegative functions,
$$\int e^{\sigma X}\, d\mu = \int \sum_k T_k\, d\mu = \sum_k \int T_k\, d\mu < \infty,$$
since the series of the terms is summable. So $e^{\sigma X}$ is integrable, and $\sigma \in S$. $\square$

The lemma is Step 3 of the local theorem of Section 3, in the language of the source. It is stated with less than the local theorem uses. It does not ask $g$ to be analytic on a disc, only that its Taylor series at $z$ is summable at the one point $\sigma$. It does not conclude that $M(\sigma) = g(\sigma)$.

**Remark (Formalization).** Three points. (a) A summable series in Mathlib is one whose finite partial sums converge along the filter of finite sets. In $\mathbb{C}$ this is absolute convergence. Here the terms are nonnegative reals, so all senses agree. (b) The $k$-th derivative of a function that is not differentiable is $0$ in Mathlib. This junk value does not occur, because $g$ is equal near $z$ to $M$, which is analytic at $z$. (c) The lemma asks $X \leq 0$ at every point of $\mathbb{R}$, not only $\mu$-almost everywhere. This is why the source takes $X(v) = -|v|$ and not $X(v) = -v$: the measure lives on $(0, \infty)$, where the two agree, but $-v$ is positive for $v < 0$.

### Landau's lemma of the source and the classical theorem

[Lemma](/decl/New.exists_Ioi_subset_integrableExpSet_of_analyticAt/) of Volume 1 says: let $X \leq 0$ be measurable, let every $t > a$ lie in the interior of $S$, and let $g$ be analytic at $a$ and equal to $M$ near every real $x > a$ close enough to $a$; then $(b, \infty) \subset S$ for some $b < a$. Its proof applies the Taylor step at a real $z \in (a, a + \varepsilon/2)$, where $\varepsilon$ is a radius of analyticity of $g$ at $a$, and gets $b = z - \varepsilon/2$.

**Proposition (The classical theorem from the lemma of the source).** Landau's theorem of Section 3, in the first form (no analytic continuation at $\sigma_c$), follows from [Lemma](/decl/New.exists_Ioi_subset_integrableExpSet_of_analyticAt/).

*Proof.* Let $\mu$ be a positive Borel measure on $[0, \infty)$ with finite abscissa $\sigma_c$, and suppose that $g$ is analytic on a disc $D$ about $\sigma_c$ and equal to $F$ on $D \cap \{\operatorname{Re} s > \sigma_c\}$. Use the dictionary with $X(v) = -|v|$ and $a = \sigma_c$. Every $t > \sigma_c$ lies in $S$, and $(\sigma_c, \infty)$ is open, so it lies in the interior of $S$. For real $x > \sigma_c$ in $D$, the set $D \cap \{\operatorname{Re} s > \sigma_c\}$ is a neighbourhood of $x$ on which $g = F = M$. So the lemma applies, and gives $b < \sigma_c$ with $(b, \infty) \subset S$. This contradicts the definition of $\sigma_c$. $\square$

Conversely, the lemma of the source follows from the classical theorem, by the pushforward of $\mu$ under $-X$ (Exercise 5). So the two are the same theorem.

**Remark (Formalization).** The differences are these. (a) The source works with any measure on $\mathbb{R}$ and any measurable $X \leq 0$, not with a measure on $[0, \infty)$. This is the language of Mathlib, and the dictionary shows that it costs nothing. (b) The source uses integrability, that is, absolute convergence. For a positive measure and a real exponent there is no other kind, and at complex $s$ the integrability of $e^{sX}$ is that of $e^{(\operatorname{Re} s)X}$. Section 2 proves the same fact for Dirichlet series with nonnegative coefficients: $\sigma_c = \sigma_a$. (c) The source never names the abscissa. The lemma is stated for any $a$ with $(a, \infty)$ in the interior of $S$, and its conclusion is a larger half-line. If $a$ is greater than the abscissa, the conclusion is trivial. [Theorem](/decl/New.IsPolar.landau/) defines its point $a$ as the least upper bound of $\{\beta\} \cup (\mathbb{R} \setminus S)$, which is $\max(\beta, \sigma_c)$. (d) The hypothesis on $g$ asks equality only near real points $x > a$ close to $a$, not on a half-disc. By the identity theorem the two are the same. (e) The source gets convergence on a segment of length less than $\varepsilon/2$ to the left of $a$, not the full radius $\varepsilon$ of the local theorem. Its argument needs only some $b < a$. (f) The function $M$ is a Bochner integral, which Mathlib sets to $0$ where $e^{sX}$ is not integrable. All comparisons of $g$ and $M$ are made near points of the interior of $S$, so this junk value does not enter.

### The meromorphic form

[Lemma](/decl/New.exists_Ioi_subset_integrableExpSet/) of Volume 1 is the meromorphic form: if a continuation $\Psi$ of $M$ has at most a simple pole at $a$, with residue $c$ of real part $\leq 0$, then $M$ converges on a larger half-line. Its proof shows first that $c$ is real and $\geq 0$, because $(x - a)M(x) \geq 0$ for real $x > a$. So $c = 0$, and the lemma above applies. This is the contrapositive of [Corollary](/chapter/landau-criterion/#the-model-case) (The residue at the abscissa) of Volume 1.

**Remark (Formalization).** The hypothesis is $\operatorname{Re} c \leq 0$ and not $c = 0$. The application in [Theorem](/decl/New.IsPolar.landau/) knows of the residue $c = -r(a)$ only the sign of its real part, from the hypothesis $\operatorname{Re} r(x) \geq 0$. The proof gets $c = 0$ from the positivity of $M$. So the hypothesis on the residues at the real points of [Theorem](/decl/New.IsPolar.landau/) is only on the real part, and it is enough. In the application to the prime remainder, $r$ is real at real points.

### The constant and the identity theorem

**Lemma (The constant).** Let $E : \mathbb{R} \to \mathbb{R}$ satisfy $|E(v)| \leq C e^v$ for every $v \geq 0$, and let $\beta > 0$. Suppose that $E(v) \leq e^{(\beta - 1)v}$ for all large $v$. Then there is a real $K$ with $E(v)e^v \leq K e^{\beta v}$ for every $v > 0$.

Lean: `New.exists_mul_exp_le` (Lib/Analytic/Landau.lean).

*Proof.* Let $Y$ be such that $E(v) \leq e^{(\beta - 1)v}$ for $v \geq Y$, and put $K = \max(1, |C| e^{2Y})$. For $v \geq Y$, $E(v)e^v \leq e^{\beta v} \leq K e^{\beta v}$. For $0 < v < Y$, $E(v) e^v \leq |C| e^{2v} \leq |C| e^{2Y} \leq K \leq K e^{\beta v}$, since $\beta v > 0$. $\square$

**Remark (Formalization).** The hypothesis $\beta > 0$ is used only in the last inequality, and it is not needed: for any real $\beta$ the constant $K = \max(1, |C| e^{(2 + |\beta|)Y})$ works, since $e^{2v} = e^{(2 - \beta)v} e^{\beta v} \leq e^{(2 + |\beta|)Y} e^{\beta v}$ for $0 < v < Y$. So $\beta > 0$ is a convenience here. It is a true hypothesis of [Theorem](/decl/New.IsPolar.landau/) for another reason: a polar function gives its residues only in $\operatorname{Re} s > 0$, and the proof needs them at every point to the right of $\beta$. In the application $\beta > 1/2$, and the criterion passes $\beta > 0$ by linear arithmetic.

**Lemma (The identity theorem far to the right).** Let $a$ and $b$ be real, and let $f, g : \mathbb{C} \to \mathbb{C}$ be meromorphic on the half-plane $\operatorname{Re} z > a$ with $f(z) = g(z)$ for every $z$ with $\operatorname{Re} z > b$. Then for every $\rho$ with $\operatorname{Re} \rho > a$, $f = g$ on a punctured neighbourhood of $\rho$.

Lean: `New.eventuallyEq_of_eq_far_right` (Lib/Analytic/Landau.lean).

*Proof.* Let $s_0$ be real with $s_0 > \max(a, b)$. The meromorphic function $f - g$ vanishes on a neighbourhood of $s_0$, so its order at $s_0$ is infinite. The half-plane $\operatorname{Re} z > a$ is convex, so connected. On a connected open set, the order of a meromorphic function is infinite at one point only if it is infinite at every point. So the order of $f - g$ at $\rho$ is infinite, and $f - g = 0$ on a punctured neighbourhood of $\rho$. $\square$

The conclusion is on punctured neighbourhoods, because Mathlib's notion of a meromorphic function puts no condition on its values at its poles. [Theorem](/decl/New.IsPolar.landau/) uses the lemma with $f = K/(s - \beta) - \Phi$ and $g = M$ on $\operatorname{Re} s > a$. It replaces the connectedness argument of the corollary on continuation along the real axis in Section 3.

### What the argument uses

The argument of the source uses one result of this chapter: [Theorem](/decl/New.IsPolar.landau/), once, in the proof of `New.LFunction_ne_zero_of_primeRemainder_le` ([Criterion.lean](lean:New/Reduction/Zeros/Criterion.lean#L78)). The other results of `Lib/Analytic/Landau.lean` are used only inside its proof. The classical forms of Section 3 for Dirichlet series and for Mellin integrals, Pringsheim's theorem, the proof that $L(1, \chi) \neq 0$, and the oscillation theorem of Section 4 are not in the source. The source needs neither the full radius of the local theorem nor the abscissa as a named object.

The inputs from Mathlib are standard analysis: the analyticity of $M$ and the formula for its derivatives on the interior of $S$, the convergence of the Taylor series of an analytic function on a disc, the theorem of Tonelli for series, the identity theorem for meromorphic functions on a connected set, and the existence of a least upper bound. No input from number theory enters the lemma. The number theory is in the polar function of the prime remainder ([the weighted prime remainder](/chapter/weighted-prime-remainder/)) and in the sign of its residues ([Landau's criterion](/chapter/landau-criterion/)).

The one sign that the argument uses is the sign of the density $K e^{\beta v} - E(v)e^v$, made nonnegative by the one-sided bound and the constant above. The weights of the prime remainder have one sign too, but the proof of the lemma does not use that sign. It enters only through the residues, at the real points.
