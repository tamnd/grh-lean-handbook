---
title: Forms of a type
lean:
  - Lib/Adelic/Unitary/Defs.lean
  - Lib/Adelic/AutomorphicForms/Basic.lean
  - Lib/Adelic/AutomorphicForms/RealConvolution.lean
  - Lib/General/Measure/IdempotentKernel.lean
decls:
  - New.HasLevel
  - New.realConv
  - New.finRightRep
  - New.Space.IsAutomorphic
  - New.Space.IsAutomorphic.comp_mul_right
  - New.Space.petersson
  - New.Space.IsAutomorphic.eq_zero_of_petersson_self
  - New.Space.IsForm
  - New.Space.IsForm.comp_mul_right
  - New.Space.formSubmodule
  - New.Space.Form
  - New.Space.Form.petersson_eq_inner_toL2
  - New.Space.peterssonCore
  - New.Space.formRep
  - New.Space.mem_levelSpace_formRep_iff
  - New.IsIdempotentKernel
  - New.IsIdempotentKernel.convolution_self
  - New.typeKernel
  - New.isIdempotentKernel_typeKernel
  - New.IsCuspKernel
  - New.isCuspKernel_typeKernel
  - New.Space.exists_form_eq_realConv
  - New.Space.exists_form_eq_tsum
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Forms of a type

This section gives the source's automorphic forms on $V$ of any signature: bounded functions on $G = G_\infty \times G_f$, left invariant under rational points, with a level, and fixed by convolution with a kernel $e$ on $G_\infty$. The kernel replaces the $K_\infty$-finiteness and $\mathfrak{z}$-finiteness of Borel and Jacquet (Section 2).

Throughout, $V = (J, x)$ is a hermitian space over $E$ with signs $s$, and $\Gamma_V \subset G$ is its group of rational points.

### Automorphic functions

**Definition (Level).** Let $K$ be a subset of $G_f$. A function $F$ on $G$ *has level $K$* if $F(g \cdot (1, k)) = F(g)$ for all $k \in K$ and $g \in G$.

Lean: `New.HasLevel` (Lib/Adelic/Unitary/Defs.lean).

**Definition (Automorphic function).** A function $F : G \to \mathbb{C}$ is *automorphic* for $V$ if it is continuous, $F(\gamma g) = F(g)$ for all $\gamma \in \Gamma_V$ and $g \in G$, and $F$ has level $K$ for some open subgroup $K$ of $G_f$.

Lean: `New.Space.IsAutomorphic` (Lib/Adelic/AutomorphicForms/Basic.lean).

Since $K \cap K_0$ is open, $F$ has a level in the sense of [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/). The right translate $g \mapsto F(ga)$ by $a \in G$ is automorphic, with level $a_f K a_f^{-1}$.

Lean: `New.Space.IsAutomorphic.comp_mul_right` (Lib/Adelic/AutomorphicForms/Basic.lean).

**Definition (Petersson product).** For functions $F, F'$ on $G$, the *Petersson product* is
$$\langle F, F' \rangle = \int_{\Gamma_V \backslash G} \overline{F(g)}\, F'(g)\, dg,$$
taken for the quotient measure of [reduction theory](/chapter/reduction-theory/).

Lean: `New.Space.petersson` (Lib/Adelic/AutomorphicForms/Basic.lean).

**Remark (Formalization).** The source forms no quotient space. Its quotient measure is the Haar measure of $G$ times a cutoff $\eta$ with $\sum_{\gamma \in \Gamma_V} \eta(\gamma g) = 1$; the Haar measure is the product of that of [discrete series](/chapter/discrete-series/) on $G_\infty$ and $\operatorname{vol}(K_0) = 1$ on $G_f$. The product is a Bochner integral, $0$ if the integrand is not integrable. For forms the integrand is bounded and the volume is finite, so it converges.

**Lemma (Definiteness).** Let $F$ be automorphic and square integrable on $\Gamma_V \backslash G$, with $\langle F, F \rangle = 0$. Then $F = 0$.

Lean: `New.Space.IsAutomorphic.eq_zero_of_petersson_self` (Lib/Adelic/AutomorphicForms/Basic.lean).

*Proof.* $F = 0$ almost everywhere for the quotient measure. The set $\{F \neq 0\}$ is open and $\Gamma_V$-invariant, so it has Haar measure $0$ and is empty. $\square$

### Convolution over the real points

**Definition (Real convolution).** For a function $k$ on $G_\infty$ and $F$ on $G$, the *right convolution* of $F$ by $k$ is
$$R(k)F(g) = \int_{G_\infty} k(x)\, F(g\,(x, 1))\, dx.$$

Lean: `New.realConv` (Lib/Adelic/AutomorphicForms/Basic.lean).

The group $G_f$ acts by right translation, $(a \cdot F)(g) = F(g\,(1, a))$, and this commutes with $R(k)$.

Lean: `New.finRightRep` (Lib/Adelic/AutomorphicForms/Basic.lean).

**Definition (Idempotent kernel).** A function $e$ on a locally compact group with a Haar measure is an *idempotent kernel* if it is continuous and integrable, $e(g^{-1}) = \overline{e(g)}$, $e(1) \neq 0$, and
$$\int e(z)\, e((zx)^{-1}y)\, dz = \frac{e(x^{-1})}{e(1)}\, e(y)$$
for all $x$ and $y$.

Lean: `New.IsIdempotentKernel` (Lib/General/Measure/IdempotentKernel.lean).

At $x = 1$ the identity says $e * e = e$ for the convolution $(e * e)(y) = \int e(z)e(z^{-1}y)\,dz$.

Lean: `New.IsIdempotentKernel.convolution_self` (Lib/General/Measure/IdempotentKernel.lean).

The model case is $e(g) = d_\pi \overline{\langle \pi(g)v, v \rangle}$ for a square integrable irreducible unitary $\pi$ of formal degree $d_\pi$ and a unit vector $v$; the orthogonality relations give the identity, and $R(e)$ is a projection.

### Forms of type $e$

**Definition (Form of type $e$).** Let $e$ be a function on $G_\infty$. A function $F$ on $G$ is a *form of type $e$* for $V$ if $F$ is automorphic, $F$ is bounded, and, if $e$ is integrable, $R(e)F = F$.

Lean: `New.Space.IsForm` (Lib/Adelic/AutomorphicForms/Basic.lean).

**Remark (Formalization).** For $e$ not integrable the last condition is empty, as the source's docstring says (finding F-036). The argument uses only the kernels $e_\lambda$, which are integrable, so the condition is never empty there. Boundedness replaces moderate growth; for a cusp kernel, forms decay rapidly (Section 5), so the space is the same.

Right translates by $a \in G_f$ and linear combinations of forms of type $e$ are forms of type $e$.

Lean: `New.Space.IsForm.comp_mul_right`, `New.Space.formSubmodule`, `New.Space.Form` (Lib/Adelic/AutomorphicForms/Basic.lean).

**Proposition (Inner product).** A form of type $e$ is square integrable on $\Gamma_V \backslash G$. The Petersson product of two forms of type $e$ is the inner product of their classes in $L^2(\Gamma_V \backslash G)$. It is a positive definite inner product on the space of forms of type $e$.

Lean: `New.Space.Form.petersson_eq_inner_toL2`, `New.Space.peterssonCore` (Lib/Adelic/AutomorphicForms/Basic.lean).

*Proof.* A form is bounded and the quotient measure is finite ([reduction theory](/chapter/reduction-theory/)). The class in $L^2$ agrees with $F$ almost everywhere. Definiteness is the lemma above. $\square$

The group $G_f$ acts on this inner product space by right translation, and a form lies in the level space of $K$ if and only if it has level $K$.

Lean: `New.Space.formRep`, `New.Space.mem_levelSpace_formRep_iff` (Lib/Adelic/AutomorphicForms/Basic.lean).

### The kernels of discrete series

For each infinite place $w$ of $E$, let $l_w = 2\lambda_w : n \to \mathbb{Z}$ be a doubled Harish-Chandra parameter for $U(\operatorname{diag} s)$, with coefficient $c_l$ of the minimal $K$-type and formal degree $d_l = (\int |c_l|^2)^{-1}$, as in [discrete series](/chapter/discrete-series/).

**Definition (Kernel of type $\lambda$).** The *kernel of type $\lambda$* is the function $e_\lambda(x) = \prod_w d_{l_w}\, \overline{c_{l_w}(x_w)}$ on $G_\infty$.

Lean: `New.typeKernel` (Lib/Adelic/AutomorphicForms/Basic.lean).

A parameter $l$ *has gap $h$* if its entries are distinct, each has the parity of $\#n - 1$, and $|l_i - l_j| \geq 2h$ whenever $s_i \neq s_j$. It *has large gap $B$* if it has gap $500\,(\#n)^3 + B$.

**Theorem.** Let $n$ be nonempty, $B \geq 0$, and suppose that $l_w$ has large gap $B$ for every infinite place $w$. Then $e_\lambda$ is an idempotent kernel on $G_\infty$.

Lean: `New.isIdempotentKernel_typeKernel` (Lib/Adelic/AutomorphicForms/RealConvolution.lean).

*Proof.* Each factor $d_{l_w}\overline{c_{l_w}}$ is an idempotent kernel by the orthogonality relations of [discrete series](/chapter/discrete-series/), and the properties pass to the product by Fubini's theorem. $\square$

**Remark (Formalization).** In $d_l = (\int |c_l|^2)^{-1}$ a divergent integral is $0$ and $0^{-1} = 0$. The gap makes $c_l$ square integrable, so $d_l > 0$. The constant $500\,(\#n)^3$ is not sharp.

For $x \in G_\infty$ let $\|x\| = \prod_w \|x_w\|$, the product of the operator norms.

**Definition (Cusp kernel).** An idempotent kernel $e$ on $G_\infty$ is a *cusp kernel of order $B$* if (a) $\|x\|^{B+1}|e(x)|$ is integrable, (b) $\int \alpha(x)\,e(x^{-1}y)\,dx = e(y)$ for some continuous function $\alpha$ with compact support, and (c) $\|x\|^B |e(x)|$ is bounded.

Lean: `New.IsCuspKernel` (Lib/Adelic/AutomorphicForms/RealConvolution.lean).

**Theorem.** Under the hypotheses of the last theorem, $e_\lambda$ is a cusp kernel of order $B$. The bound in (c) is $\prod_w d_{l_w} 2^B$.

Lean: `New.isCuspKernel_typeKernel` (Lib/Adelic/AutomorphicForms/RealConvolution.lean).

*Proof.* Take products of the local properties from [discrete series](/chapter/discrete-series/). $\square$

**Remark (Formalization).** The local functions of (b) come by `choose`; only their existence enters. Condition (b) gives the continuity estimates of Section 5 without derivatives.

### Making forms

**Proposition.** Let $e$ be an idempotent kernel on $G_\infty$, $K$ an open subgroup of $G_f$, and $F$ a bounded measurable function on $G$ that is left $\Gamma_V$-invariant and has level $K$. Then $R(e)F$ is a form of type $e$ of level $K$.

Lean: `New.Space.exists_form_eq_realConv` (Lib/Adelic/AutomorphicForms/RealConvolution.lean).

*Proof.* $R(e)F$ is continuous, bounded by $\|e\|_1 \sup |F|$, keeps invariance and level, and $R(e)R(e) = R(e * e) = R(e)$. $\square$

**Theorem (Poincaré series).** Let $e$ be an idempotent kernel on $G_\infty$ and $K$ an open subgroup of $G_f$. Let $(W_i)_{i \in I}$ be a countable family of measurable functions on $G$, with $\sum_i |W_i(g)| \leq M < \infty$ for all $g$. Let $c$ be a function on $G$ of level $K$ with $\sum_{\gamma \in \Gamma_V} c(\gamma g) = \sum_i W_i(g)$ for all $g$. Then $g \mapsto \sum_i R(e)W_i(g)$ is a form of type $e$ of level $K$.

Lean: `New.Space.exists_form_eq_tsum` (Lib/Adelic/AutomorphicForms/RealConvolution.lean).

*Proof.* $\sum_i W_i$ is bounded, measurable, left $\Gamma_V$-invariant and of level $K$, so the proposition applies. Dominated convergence exchanges sum and convolution. $\square$

**Remark (Formalization).** The sums are `tsum`, $0$ if not summable. The bound makes the sum over $I$ converge. If the sum over $\Gamma_V$ diverges, the hypothesis says $\sum_i W_i = 0$, and the conclusion still holds. In the argument the hypothesis is the unfolding of a Poincaré series.

### Where the argument uses forms of a type

Forms of type $e$: [Hecke values](/chapter/hecke-values/), [single theta lifts](/chapter/single-theta-lifts/), [the exchange identity](/chapter/exchange-identity-2/), [grids, columns and turns](/chapter/grids-paths-turns/), [Poincaré series](/chapter/poincare-series/). Cusp kernels: [upper bound objects](/chapter/upper-bound-objects/), [grids, columns and turns](/chapter/grids-paths-turns/).
