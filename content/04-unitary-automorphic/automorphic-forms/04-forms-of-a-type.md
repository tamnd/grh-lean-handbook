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

This section gives the source's automorphic forms on a hermitian space $V$ of any signature. They are functions on $G = G_\infty \times G_f$ that are invariant under the rational points on the left, have a level on the right, are bounded, and are fixed by convolution with a kernel $e$ on $G_\infty$. The kernel takes the place of the $K_\infty$-finiteness and $\mathfrak{z}$-finiteness of Borel and Jacquet (Section 2). For the kernels $e_\lambda$ of discrete series, the forms of type $e_\lambda$ are the forms that generate the discrete series of parameter $\lambda$ at the infinite places.

Throughout, $V = (J, x)$ is a hermitian space over $E$ with signs $s$, and $\Gamma_V \subset G$ is its group of rational points.

### Automorphic functions

**Definition (Level).** Let $K$ be a subset of $G_f$. A function $F$ on $G$ *has level $K$* if $F(g \cdot (1, k)) = F(g)$ for all $k \in K$ and $g \in G$.

Lean: `New.HasLevel` (Lib/Adelic/Unitary/Defs.lean).

**Definition (Automorphic function).** A function $F : G \to \mathbb{C}$ is *automorphic* for $V$ if it is continuous, $F(\gamma g) = F(g)$ for all $\gamma \in \Gamma_V$ and $g \in G$, and $F$ has level $K$ for some open subgroup $K$ of $G_f$.

Lean: `New.Space.IsAutomorphic` (Lib/Adelic/AutomorphicForms/Basic.lean).

The level need not lie in $K_0$. Since $K \cap K_0$ is again open, an automorphic function always has a level in the sense of [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/). The right translate $g \mapsto F(ga)$ of an automorphic function by $a \in G$ is automorphic, with level $a_f K a_f^{-1}$, since $F(g\,(1, k)\,a) = F(ga\,(1, a_f^{-1}ka_f))$.

Lean: `New.Space.IsAutomorphic.comp_mul_right` (Lib/Adelic/AutomorphicForms/Basic.lean).

**Definition (Petersson product).** For functions $F, F'$ on $G$, the *Petersson product* is
$$\langle F, F' \rangle = \int_{\Gamma_V \backslash G} \overline{F(g)}\, F'(g)\, dg,$$
taken for the quotient measure of [reduction theory](/chapter/reduction-theory/).

Lean: `New.Space.petersson` (Lib/Adelic/AutomorphicForms/Basic.lean).

**Remark (Formalization).** The source does not form the quotient space $\Gamma_V \backslash G$. Its quotient measure is a measure on $G$ itself: the Haar measure of $G$ times a cutoff function $\eta$ with $\sum_{\gamma \in \Gamma_V} \eta(\gamma g) = 1$. Integrals of left $\Gamma_V$-invariant functions against it are the integrals over the quotient. The product is a Bochner integral, which is $0$ when the integrand is not integrable. For the forms of this section the integrand is bounded and the quotient has finite volume, so the integral converges. The Haar measure on $G$ is the product of the measure on $G_\infty$ from [discrete series](/chapter/discrete-series/) and the measure on $G_f$ with $\operatorname{vol}(K_0) = 1$.

**Lemma (Definiteness).** Let $F$ be automorphic and square integrable on $\Gamma_V \backslash G$, with $\langle F, F \rangle = 0$. Then $F = 0$.

Lean: `New.Space.IsAutomorphic.eq_zero_of_petersson_self` (Lib/Adelic/AutomorphicForms/Basic.lean).

*Proof.* The integral of $|F|^2$ against the quotient measure is $0$, so $F = 0$ almost everywhere for that measure. The zero set of $F$ is invariant under $\Gamma_V$, and its complement is open, since $F$ is continuous. An open set of measure $0$ for the quotient measure has a $\Gamma_V$-saturation of Haar measure $0$, so it is empty, and the zero set is dense. A continuous function that vanishes on a dense set is $0$. $\square$

### Convolution over the real points

**Definition (Real convolution).** For a function $k$ on $G_\infty$ and $F$ on $G$, the *right convolution* of $F$ by $k$ is
$$R(k)F(g) = \int_{G_\infty} k(x)\, F(g\,(x, 1))\, dx.$$

Lean: `New.realConv` (Lib/Adelic/AutomorphicForms/Basic.lean).

The group $G_f$ acts on functions on $G$ by right translation, $(a \cdot F)(g) = F(g\,(1, a))$. This action commutes with $R(k)$, since $(x, 1)$ and $(1, a)$ commute in $G$.

Lean: `New.finRightRep` (Lib/Adelic/AutomorphicForms/Basic.lean).

**Definition (Idempotent kernel).** A function $e$ on a locally compact group with a Haar measure is an *idempotent kernel* if it is continuous and integrable, $e(g^{-1}) = \overline{e(g)}$, $e(1) \neq 0$, and
$$\int e(z)\, e((zx)^{-1}y)\, dz = \frac{e(x^{-1})}{e(1)}\, e(y)$$
for all $x$ and $y$.

Lean: `New.IsIdempotentKernel` (Lib/General/Measure/IdempotentKernel.lean).

At $x = 1$ the identity says $e * e = e$ for the convolution $(e * e)(y) = \int e(z)e(z^{-1}y)\,dz$.

Lean: `New.IsIdempotentKernel.convolution_self` (Lib/General/Measure/IdempotentKernel.lean).

The model case is a matrix coefficient. Let $\pi$ be a square integrable irreducible unitary representation with formal degree $d_\pi$, and let $v$ be a unit vector. Put $e(g) = d_\pi \overline{\langle \pi(g)v, v \rangle}$. The orthogonality relations for square integrable representations give the identity above: the general identity says that $e * \delta_x * e$ is a multiple of $e$, and this holds because $e$ is $d_\pi$ times the coefficient of the rank one projection onto $\mathbb{C}v$. So $R(e)$ acts on a unitary representation as a projection, and it is $0$ unless the representation contains $\pi$.

### Forms of type $e$

**Definition (Form of type $e$).** Let $e$ be a function on $G_\infty$. A function $F$ on $G$ is a *form of type $e$* for $V$ if $F$ is automorphic, $F$ is bounded, and, if $e$ is integrable, $R(e)F = F$.

Lean: `New.Space.IsForm` (Lib/Adelic/AutomorphicForms/Basic.lean).

**Remark (Formalization).** For $e$ not integrable the last condition is empty, so every bounded automorphic function is then a form of type $e$. The docstring of the source says so. The list of findings of the plan of the book records this (F-036). The argument uses forms of type $e$ only for the kernels $e_\lambda$ below, and these are integrable by the theorem on $e_\lambda$. So the condition is never empty where the argument uses it. The source asks for boundedness in place of moderate growth. Section 5 shows that, for a cusp kernel, a form of type $e$ decays rapidly, so the two growth conditions give the same space.

The right translate of a form of type $e$ by a point $a \in G_f$ is again a form of type $e$. Linear combinations of forms of type $e$ are forms of type $e$, so they make up a subspace.

Lean: `New.Space.IsForm.comp_mul_right`, `New.Space.formSubmodule`, `New.Space.Form` (Lib/Adelic/AutomorphicForms/Basic.lean).

**Proposition (Inner product).** A form of type $e$ is square integrable on $\Gamma_V \backslash G$. The Petersson product of two forms of type $e$ is the inner product of their classes in $L^2(\Gamma_V \backslash G)$. It is a positive definite inner product on the space of forms of type $e$.

Lean: `New.Space.Form.petersson_eq_inner_toL2`, `New.Space.peterssonCore` (Lib/Adelic/AutomorphicForms/Basic.lean).

*Proof.* A form is bounded and continuous, and the quotient measure is finite ([reduction theory](/chapter/reduction-theory/)), so it is square integrable. The two integrals agree since the class of $F$ in $L^2$ agrees with $F$ almost everywhere. Symmetry, positivity and sesquilinearity hold for the inner product of $L^2$. Definiteness is the lemma above, which uses that forms are continuous. $\square$

So the forms of type $e$ make up a complex inner product space. The finite group $G_f$ acts on it by right translation, $(a \cdot F)(g) = F(g\,(1, a))$, and a form lies in the level space of a subgroup $K$ of $G_f$ if and only if it has level $K$.

Lean: `New.Space.formRep`, `New.Space.mem_levelSpace_formRep_iff` (Lib/Adelic/AutomorphicForms/Basic.lean).

### The kernels of discrete series

The source uses one family of kernels. Let $w$ run over the infinite places of $E$. For each $w$, let $l_w : n \to \mathbb{Z}$ be the doubled Harish-Chandra parameter $l_w = 2\lambda_w$ of a discrete series of $U(\operatorname{diag} s)$, as in [discrete series](/chapter/discrete-series/). That chapter gives the coefficient $c_{l}$ of the minimal $K$-type and the formal degree $d_l = (\int |c_l|^2)^{-1}$.

**Definition (Kernel of type $\lambda$).** The *kernel of type $\lambda$* is the function $e_\lambda(x) = \prod_w d_{l_w}\, \overline{c_{l_w}(x_w)}$ on $G_\infty$.

Lean: `New.typeKernel` (Lib/Adelic/AutomorphicForms/Basic.lean).

A parameter $l$ for the signs $s$ *has gap $h$* if its entries are distinct, each $l_i$ has the parity of $\#n - 1$, and $|l_i - l_j| \geq 2h$ whenever $s_i \neq s_j$. It *has large gap $B$* if it has gap $500\,(\#n)^3 + B$. Both notions are from [discrete series](/chapter/discrete-series/).

**Theorem.** Let $n$ be nonempty, $B \geq 0$, and suppose that $l_w$ has large gap $B$ for every infinite place $w$. Then $e_\lambda$ is an idempotent kernel on $G_\infty$.

Lean: `New.isIdempotentKernel_typeKernel` (Lib/Adelic/AutomorphicForms/RealConvolution.lean).

*Proof.* The group $G_\infty$ is a product over $w$, its Haar measure is the product measure, and $e_\lambda$ is a product. Each property of an idempotent kernel is a statement about one function and one integral, and it passes to products by Fubini's theorem. Each factor $d_{l_w}\overline{c_{l_w}}$ is an idempotent kernel on $U(\operatorname{diag} s)$ by the orthogonality relations, which [discrete series](/chapter/discrete-series/) proves under the gap condition. $\square$

**Remark (Formalization).** The formal degree is defined as $(\int |c_l|^2)^{-1}$, with the junk values $\int = 0$ for a function that is not square integrable and $0^{-1} = 0$. The gap condition makes $c_l$ square integrable, so $d_l > 0$ in the theorem. The constant $500\,(\#n)^3$ is a convenient bound of the source, not a sharp one.

A finer notion is needed for finite dimension and decay. For $x \in G_\infty$ let $\|x\| = \prod_w \|x_w\|$, the product of the operator norms.

**Definition (Cusp kernel).** An idempotent kernel $e$ on $G_\infty$ is a *cusp kernel of order $B$* if (a) $\|x\|^{B+1}|e(x)|$ is integrable, (b) $\int \alpha(x)\,e(x^{-1}y)\,dx = e(y)$ for some continuous function $\alpha$ with compact support, and (c) $\|x\|^B |e(x)|$ is bounded.

Lean: `New.IsCuspKernel` (Lib/Adelic/AutomorphicForms/RealConvolution.lean).

**Theorem.** Under the hypotheses of the last theorem, $e_\lambda$ is a cusp kernel of order $B$. The bound in (c) is $\prod_w d_{l_w} 2^B$.

Lean: `New.isCuspKernel_typeKernel` (Lib/Adelic/AutomorphicForms/RealConvolution.lean).

*Proof.* Each of (a), (b), (c) is a product of the same property at each place, which [discrete series](/chapter/discrete-series/) gives. For (b) the bump function is the product of the local ones. $\square$

**Remark (Formalization).** In the Lean proof the local bump functions of (b) are picked by `choose`, one at each infinite place. Only their existence enters the statement. Condition (b) says that $e$ is a smooth vector: it is how the source gets the continuity estimates of Section 5 without derivatives.

### Making forms

There are two ways to make a form of type $e$. Both start from a bounded function and project it by $R(e)$.

**Proposition.** Let $e$ be an idempotent kernel on $G_\infty$, $K$ an open subgroup of $G_f$, and $F$ a bounded measurable function on $G$ that is left $\Gamma_V$-invariant and has level $K$. Then $R(e)F$ is a form of type $e$ of level $K$.

Lean: `New.Space.exists_form_eq_realConv` (Lib/Adelic/AutomorphicForms/RealConvolution.lean).

*Proof.* The convolution of a bounded function with an integrable continuous kernel is continuous and bounded by $\|e\|_1 \sup |F|$. It is left $\Gamma_V$-invariant and has level $K$ since $R(e)$ acts on the right in the variable $G_\infty$. It is fixed by $R(e)$ since $R(e)R(e) = R(e * e) = R(e)$. $\square$

**Theorem (Poincaré series).** Let $e$ be an idempotent kernel on $G_\infty$ and $K$ an open subgroup of $G_f$. Let $(W_i)_{i \in I}$ be a countable family of measurable functions on $G$, with $\sum_i |W_i(g)| \leq M < \infty$ for all $g$. Let $c$ be a function on $G$ of level $K$ with $\sum_{\gamma \in \Gamma_V} c(\gamma g) = \sum_i W_i(g)$ for all $g$. Then $g \mapsto \sum_i R(e)W_i(g)$ is a form of type $e$ of level $K$.

Lean: `New.Space.exists_form_eq_tsum` (Lib/Adelic/AutomorphicForms/RealConvolution.lean).

*Proof.* The sum $\sum_i W_i$ is bounded by $M$, measurable, left $\Gamma_V$-invariant (a reindexing of the sum over $\Gamma_V$) and of level $K$. So the proposition applies to it. The convolution of the sum is the sum of the convolutions, by dominated convergence with the bound $|e(x)| M$. $\square$

**Remark (Formalization).** The sums are Lean's `tsum`, which is $0$ for a family that is not summable. The bound on $\sum_i |W_i|$ makes the sum over $I$ converge. The sum over $\Gamma_V$ is only tied to the $W_i$ by the hypothesis. If it does not converge, the hypothesis says that $\sum_i W_i = 0$, and the conclusion still holds. In the argument the $W_i$ are the terms of a Poincaré series, grouped so that the sum of norms is bounded, and the hypothesis is the unfolding of the series.

### Where the argument uses these objects

Forms of type $e$ appear in six files of the argument, always for a kernel $e_\lambda$. They are the forms on indefinite groups in the [Hecke values](/chapter/hecke-values/) of character lifts, the norms of [single theta lifts](/chapter/single-theta-lifts/), the removal of planes in [the exchange identity](/chapter/exchange-identity-2/), the vanishing at deep level in [grids, paths and turns](/chapter/grids-paths-turns/), and the series period and the Poincaré series of [Poincaré series](/chapter/poincare-series/). The Poincaré series theorem is used once, in the proof that the Poincaré series of Theorem B are forms. The cusp kernel theorem is used in [the objects of the upper bound](/chapter/upper-bound-objects/) and in [grids, paths and turns](/chapter/grids-paths-turns/).
