---
title: The kernel and the geometric side
lean:
  - Lib/Adelic/TraceFormula/OrbitalUnfolding.lean
  - Lib/Adelic/TraceFormula/ReduciblePolynomials.lean
  - Lib/Adelic/TraceFormula/Convergence.lean
decls:
  - New.Space.partialKernel_convIndicator_eq_sum
  - New.Space.volume_mul_trace_eq
  - New.Space.geometricSide
  - New.Space.hasSum_geometricSide
  - New.Space.geometricSide_translate
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The kernel and the geometric side

This section writes the trace of a Hecke operator on forms as the integral of a kernel over the diagonal. It then splits the integral by the characteristic polynomial of the rational points. The result is the identity $\operatorname{vol}(K) \operatorname{tr} T = \sum_R I_R(a \star 1_K)$. Sections 4 to 6 compute the terms $I_R$.

### Setting

Fix $N = |n| \geq 1$, signs $s$, and a space $V$ as in Section 1, with adelic group $G = G_\infty \times G_f$. The group $\Gamma$ is the image of the rational points $U(V)(E)$ in $G$, and $[G] = \Gamma \backslash G$. Integrals over $[G]$ use the measure $dx$ of [reduction theory](/chapter/reduction-theory/), for which $[G]$ has finite volume.

A *level* is an open subgroup $K$ of the standard maximal compact subgroup $K_0$ of $G_f$. Its volume $\operatorname{vol}(K)$ is taken for the Haar measure fixed on $G_f$. It is positive.

For a function $e$ on $G_\infty$ that is integrable, a *form of type $e$* is a function $F$ on $G$ that is automorphic, bounded, and fixed by right convolution with $e$ over the real points: $\int_{G_\infty} e(y) F(g (y, 1))\, dy = F(g)$. The forms of type $e$ make a pre-Hilbert space for the Petersson product $\langle F, F' \rangle = \int_{[G]} \overline{F(x)} F'(x)\, dx$, and $G_f$ acts on it by right translation. This is the representation $\rho_e$ of [automorphic forms](/chapter/automorphic-forms/). Write $\mathcal{A}_e^K$ for the forms of type $e$ that are fixed by $K$.

**Remark (Formalization).** In the source the condition "fixed by right convolution with $e$" has the hypothesis that $e$ is integrable (`New.Space.IsForm`). For $e$ not integrable it is empty, and every bounded automorphic function is then a form of type $e$. This junk case does not occur here: a cusp kernel is integrable.

A *cusp kernel of order $B$* is a function $e$ on $G_\infty$ with the following properties. With $\|x\| = \prod_{v \mid \infty} \|x_v\|$, the product of the operator norms:

1. $e$ is continuous and integrable, $e(g^{-1}) = \overline{e(g)}$, $e(1) \neq 0$, and $\int e(z)\, e((z x)^{-1} y)\, dz = e(x^{-1}) e(y) / e(1)$ for all $x, y$;
2. $\|x\|^{B+1} |e(x)|$ is integrable;
3. $\alpha * e = e$ for some continuous function $\alpha$ of compact support;
4. $\|x\|^B |e(x)|$ is bounded.

The first item says that $e$ is a minimal idempotent for convolution. The kernels $e_\lambda$ of the discrete series are cusp kernels of order $B$ when the parameter has a gap of size $500 N^3 + B$ between entries of opposite sign (`New.isCuspKernel_typeKernel`, explained in [the discrete series](/chapter/discrete-series/)). In this section $B \geq 13 N^3$.

### The kernel

Let $e$ be a cusp kernel and let $\varphi$ be a test function on $G_f$. The kernel of $e \otimes \varphi$ is
$$ k(x, y) = \sum_{\gamma \in U(V)(E)} e\big((x^{-1} \gamma y)_\infty\big)\, \varphi\big((x^{-1} \gamma y)_f\big). $$
For $B \geq 13 N^3$ the sum converges absolutely, and $\sum_\gamma |\,\cdot\,|$ is bounded on $G \times G$ when $x = y$. This is the convergence estimate of the source (`New.Space.exists_norm_tsum_polyTerm_le`). Its proof bounds the sum by a power of the height in a Siegel domain, and high in a cusp it uses the decay of $e$. It is the reason for the order $13 N^3$.

**Theorem (Spectral expansion of the kernel).** Let $N \geq 1$ and $B \geq 13 N^3$, let $e$ be a cusp kernel of order $B$, and let $K$ be a level. Let $(b_i)$ be an orthonormal basis of $\mathcal{A}_e^K$ and let $a \in \mathbb{C}[G_f]$. Then for all $g, g' \in G$,
$$ \sum_{\gamma} \big(e \otimes (a \star 1_K)\big)(g^{-1} \gamma g') = \operatorname{vol}(K) \sum_i \big(\rho_e(a) b_i\big)(g)\, \overline{b_i(g')}. $$
Lean: `New.Space.partialKernel_convIndicator_eq_sum` (Lib/Adelic/TraceFormula/OrbitalUnfolding.lean).

*Proof.* Both sides are linear in $a$. So it suffices to take $a = h$, a point of $G_f$. Then $a \star 1_K = 1_{hK}$, and the left side is the kernel of $e \otimes 1_K$ at $(g (1, h), g')$. Let $k$ be the kernel of $e \otimes 1_K$. For fixed $g$ the function $F_g : g' \mapsto \overline{k(g, g')}$ is a form of type $e$ and level $K$ (`New.Space.exists_kernel_form`). Its Petersson product with a form $v$ of level $K$ is $\langle F_g, v \rangle = \operatorname{vol}(K)\, v(g)$ (`New.Space.inner_kernel_form`). This is the reproducing property: unfold the integral over $[G]$ against the sum over $\gamma$, integrate $1_K$ against the $K$-invariant function $v$, and use that $e$ reproduces $v$ at infinity. Expand $F_g$ in the basis $(b_i)$. This gives the case $a = 1$ (`New.Space.tsum_kernel_eq_sum`), and the case $a = h$ follows by right translation. $\square$

### The trace

**Theorem (Trace as an integral).** Let $N \geq 1$ and $B \geq 13 N^3$, let $e$ be a cusp kernel of order $B$, and let $K$ be a level. Let $a \in \mathbb{C}[G_f]$, and let $T$ be a linear operator on $\mathcal{A}_e^K$ that acts as $a$: $T y = \rho_e(a) y$ for all $y$. Then
$$ \operatorname{vol}(K) \operatorname{tr} T = \int_{[G]} \sum_{\gamma \in U(V)(E)} \big(e \otimes (a \star 1_K)\big)(x^{-1} \gamma x)\, dx. $$
Lean: `New.Space.volume_mul_trace_eq` (Lib/Adelic/TraceFormula/OrbitalUnfolding.lean).

*Proof.* The space $\mathcal{A}_e^K$ is finite-dimensional (`New.Space.finite_levelSpace`, proved in [automorphic forms](/chapter/automorphic-forms/)). Take an orthonormal basis $(b_i)$. Put $g = g' = x$ in [the spectral expansion](/decl/New.Space.partialKernel_convIndicator_eq_sum/). Integrate over $[G]$. Each term $\int_{[G]} (T b_i)(x)\, \overline{b_i(x)}\, dx$ is $\langle b_i, T b_i \rangle$, and the sum of these is $\operatorname{tr} T$. $\square$

**Remark (Formalization).** Three points of the source matter here.

1. The trace is `LinearMap.trace`. On a space with no finite basis it is $0$ by definition. Here the space is finite-dimensional, so this junk value does not enter. The theorem has no finiteness hypothesis, since the proof gets finiteness itself.
2. The measure on $[G]$ is a measure on $G$: Haar measure times a cutoff $\beta$ with $\sum_{\delta \in \Gamma} \beta(\delta x) = 1$ (`New.Space.quotMeasure`). The cutoff is chosen by `Classical.epsilon` (`New.chosenCutoff`). For $\Gamma$-invariant integrands the integral does not depend on the choice, when a cutoff exists, and every integrand of this section is $\Gamma$-invariant.
3. The identity has the factor $\operatorname{vol}(K)$ because $a \star 1_K$ is not divided by $\operatorname{vol}(K)$. This answers the question of finding F-035, which asked where the trace formula of the plan appears in the source: it is this theorem with $S$ the set of all polynomials.

### Splitting by characteristic polynomial

The characteristic polynomial $\chi_\gamma \in E[X]$ is constant on conjugacy classes. So the kernel on the diagonal splits.

**Definition (Geometric side).** Let $B \geq 13 N^3$ and let $e$ be a cusp kernel of order $B$. For a set $S$ of polynomials in $E[X]$ the *part of the geometric side given by $S$* is the linear form on test functions
$$ I_S(\varphi) = \int_{[G]} \sum_{\gamma \,:\, \chi_\gamma \in S} e\big((x^{-1} \gamma x)_\infty\big)\, \varphi\big((x^{-1} \gamma x)_f\big)\, dx. $$
Write $I_R = I_{\{R\}}$ for one polynomial $R$.
Lean: `New.Space.geometricSide` (Lib/Adelic/TraceFormula/ReduciblePolynomials.lean).

The integrand is integrable for every $S$ (`New.Space.integrable_tsum_polyTerm`), since the sum is bounded uniformly in $S$ and $x$, and $[G]$ has finite volume. With $S = E[X]$ the theorem above reads $\operatorname{vol}(K) \operatorname{tr} T = I_{E[X]}(a \star 1_K)$.

**Theorem.** Let $B \geq 13 N^3$, let $e$ be a cusp kernel of order $B$, and let $\varphi$ be a test function. The family $(I_R(\varphi))_{R \in E[X]}$ is summable with sum $I_{E[X]}(\varphi)$.
Lean: `New.Space.hasSum_geometricSide` (Lib/Adelic/TraceFormula/ReduciblePolynomials.lean).

*Proof.* For a finite set $F$ of polynomials, $I_F = \sum_{R \in F} I_R$ by linearity of the integral and of the sum over $\gamma$. As $F$ increases, the inner sums $\sum_{\chi_\gamma \in F}$ converge at each $x$ to the full sum, by dominated convergence for the absolutely convergent sum over $\gamma$. They are bounded by one constant $D$, uniformly in $F$ and $x$ (`New.Space.exists_norm_tsum_polyTerm_le`). Since $[G]$ has finite volume, dominated convergence for the integral gives $I_F(\varphi) \to I_{E[X]}(\varphi)$. $\square$

Summability here is unconditional summability over the countable set $E[X]$, the limit along the finite subsets. Only finitely many $R$ give a nonzero term for a given $\varphi$, but the proof does not need this.

The parts of the geometric side are conjugation invariant.

**Lemma.** Let $B \geq 13 N^3$ and let $e$ be a cusp kernel of order $B$. For every set $S$ of polynomials, every $g \in G_f$ and every test function $\varphi$,
$$ I_S\big(y \mapsto \varphi(g^{-1} y g)\big) = I_S(\varphi). $$
Lean: `New.Space.geometricSide_translate` (Lib/Adelic/TraceFormula/ReduciblePolynomials.lean).

*Proof.* The integrand for the conjugate test function at $x$ is the integrand for $\varphi$ at $x (1, g)$. The integrand is $\Gamma$-invariant on the left, since $\delta \in \Gamma$ permutes the $\gamma$ and keeps $\chi_\gamma$. The measure on $[G]$ is invariant under right translation for such integrands. $\square$

Section 4 uses this lemma to replace $\varphi$ by its mean over the conjugates by a compact group.

### A model case

Take $N = 1$. Then $U(V)$ is the norm one torus $E^1$, and every $\gamma$ is a scalar with $\chi_\gamma = X - \gamma$. The group $G$ is commutative, so $x^{-1} \gamma x = \gamma$ and the integrand does not depend on $x$. So
$$ I_{\{X - \gamma\}}(\varphi) = \operatorname{vol}([G])\, e(\gamma_\infty)\, \varphi(\gamma_f). $$
The trace identity becomes $\operatorname{vol}(K) \operatorname{tr} T = \operatorname{vol}([G]) \sum_{\gamma \in E^1} e(\gamma_\infty) (a \star 1_K)(\gamma_f)$. The sum is finite: $\gamma_f$ must lie in the compact set $\operatorname{supp}(a) K$, and $\gamma$ is then in a discrete subset of a compact set. For $N = 1$ every $\chi_\gamma$ is irreducible, and Sections 4 and 5 have nothing to do. The comparison of Section 6 is then the comparison of these finite sums for two choices of signs at infinity.
