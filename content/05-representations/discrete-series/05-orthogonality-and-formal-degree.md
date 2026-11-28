---
title: Orthogonality, rigidity and the formal degree
lean:
  - Lib/DiscreteSeries/FlenstedJensen/SquareIntegrability.lean
  - Lib/DiscreteSeries/Rigidity/RepresentationsAndCasimirs.lean
  - Lib/DiscreteSeries/Rigidity/KernelFixes.lean
  - Lib/General/Measure/IdempotentKernel.lean
  - Lib/DiscreteSeries/Character/WeylCharacterFormula.lean
  - Lib/DiscreteSeries/Character/FormalDegree.lean
decls:
  - New.formalDegree_pos
  - New.HCParam.dsKernel
  - New.dsCoeff_schur_orthogonality
  - New.HCParam.IsKHighest
  - New.HCParam.DsModule
  - New.isKHighest_dsGenerator
  - New.IsUnitaryCasimirGe
  - New.HCParam.HasLargeGap.isUnitaryCasimirGe_dsAction
  - New.IsIdempotentKernel
  - New.IsIdempotentKernel.convolution_self
  - New.HCParam.HasLargeGap.isIdempotentKernel_dsKernel
  - New.HCParam.HasLargeGap.exists_bump_conv_dsKernel
  - New.IsUnitaryRep
  - New.IsDerivedAction
  - New.coeff_eq_dsCoeff_of_isKHighest
  - New.weyl_dimension_formula
  - New.HCParam.kTypeChar
  - New.Orbital.formalDegree_eq_weylDimensionPoly
  - New.Orbital.harish_chandra_degree_and_orbital
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Orthogonality, rigidity and the formal degree

This section proves the three facts that make $c_\lambda$ behave like the coefficient of a discrete series. First, Schur orthogonality, so that $e_\lambda = d_\lambda\overline{c_\lambda}$ is an idempotent for convolution. Second, rigidity: in any unitary representation of polynomial growth, a vector of the right $K$-type and Casimir value has the coefficient $c_\lambda$. Third, Harish-Chandra's formula: $d_\lambda$ is a Weyl dimension, and the stable orbital integrals of $e_\lambda$ on the compact torus give Weyl's character. All results need a large gap $500n^3 + A$, and $n \ge 1$.

### Schur orthogonality

**Theorem.** Let $n \ge 1$, and let $l = 2\lambda$ have gap $500n^3 + A$. Then $d_\lambda > 0$.

Lean: `New.formalDegree_pos` (Lib/DiscreteSeries/FlenstedJensen/SquareIntegrability.lean).

*Proof.* The function $|c_\lambda|^2$ is continuous, nonnegative and equal to $1$ at $1$. It is integrable because $c_\lambda$ lies in the module $U(\mathfrak g)c_\lambda$, all of whose elements are square integrable for a large gap (`New.HCParam.HasLargeGap.memLp`). So $\int_G|c_\lambda|^2 > 0$, and $d_\lambda$ is its inverse. $\square$

So under a large gap the junk value $0$ of Section 3 does not occur, and $e_\lambda = d_\lambda\overline{c_\lambda}$ is not $0$.

Lean: `New.HCParam.dsKernel` (Lib/DiscreteSeries/FlenstedJensen/Defs.lean).

**Theorem (Schur orthogonality).** Let $n \ge 1$, let $l = 2\lambda$ have gap $500n^3 + A$, and let $x, a \in G$. Then

$$d_\lambda\int_G c_\lambda(xya)\,\overline{c_\lambda(y)}\,dy = c_\lambda(x)\,c_\lambda(a).$$

Lean: `New.dsCoeff_schur_orthogonality` (Lib/DiscreteSeries/FlenstedJensen/SquareIntegrability.lean).

For the coefficient $c(g) = \langle \pi(g)v, v\rangle$ of a unit vector, the left side is $d_\pi\int_G\langle\pi(x)\pi(y)\pi(a)v, v\rangle\overline{\langle\pi(y)v,v\rangle}\,dy$, and Schur's relation $\int_G \langle \pi(y)u, v\rangle\overline{\langle\pi(y)u', v'\rangle}dy = d_\pi^{-1}\langle u, u'\rangle\overline{\langle v, v'\rangle}$ gives $\langle\pi(a)v, v\rangle\langle\pi(x)v, v\rangle$. The source has no $\pi$. It uses the projection to the lowest $K$-type of Section 4 in place of the irreducibility.

*Proof.* Step 1. Let $w$ be integrable on $G$ with $\int_K\overline{m_\Lambda(k)}\,w(k^{-1}g)\,dk = N\,w(g)$ for all $g$, where $N = \int_K|m_\Lambda|^2$. Then $\int_G w(g)\,c_\lambda(xga)\,dg = c_\lambda(x)\int_G w(g)\,c_\lambda(ga)\,dg$ (`New.integral_mul_dsCoeff_translate`). Indeed, compute $\int_K\int_G \overline{m_\Lambda(k)}\,w(g)\,c_\lambda(xkga)\,dg\,dk$ in two ways. The substitution $g \mapsto k^{-1}g$ and the hypothesis on $w$ give $N$ times the left side. The projection theorem of Section 4 with the points $x$ and $ga$ gives $N\,c_\lambda(x)$ times the right side. Fubini applies because $|c_\lambda| \le 1$, $K$ is compact and $w$ is integrable. Cancel $N > 0$.

Step 2. Take $w(g) = c_\lambda(g^{-1})$. It is integrable. The projection theorem with the points $g^{-1}$ and $1$ gives $\int_K\overline{m_\Lambda(k)}\,c_\lambda(g^{-1}k)\,dk = N\,c_\lambda(g^{-1})c_\lambda(1) = N\,w(g)$. So Step 1 applies:

$$\int_G c_\lambda(g^{-1})\,c_\lambda(xga)\,dg = c_\lambda(x)\int_G c_\lambda(g^{-1})\,c_\lambda(ga)\,dg.$$

Step 3. Use Step 2 with the points $a$ and $1$, and substitute $g \mapsto a^{-1}g^{-1}$, which preserves the Haar measure of $G$. This moves $a$ from the left to the right: $\int_G c_\lambda(g^{-1})c_\lambda(ga)\,dg = c_\lambda(a)\int_G c_\lambda(g^{-1})c_\lambda(g)\,dg$.

Step 4. By $c_\lambda(g^{-1}) = \overline{c_\lambda(g)}$, the last integral is $\int_G|c_\lambda|^2 = d_\lambda^{-1}$. Combine Steps 2 to 4, and use $c_\lambda(g^{-1}) = \overline{c_\lambda(g)}$ once more to write the integrand in the form of the statement. $\square$

**Example.** In $U(1,1)$ take $x = a = 1$. The theorem says $d_\lambda\int_G|c_\lambda|^2 = 1$, which is the definition. For $x = \operatorname{diag}(e^{i\alpha}, e^{i\beta})$ in $K$, $c_\lambda(xy) = e^{-ik\alpha}e^{i(\alpha + \beta)w_2}c_\lambda(y)$ by the formula $c_\lambda(g) = g_{11}^{-k}(\det g)^{w_2}$, and this factor is $m_\Lambda(x) = e^{i(w_1\alpha + w_2\beta)}$, since $w_1 = w_2 - k$. So the theorem holds for such $x$ and $a = 1$.

### The module $U(\mathfrak g)c_\lambda$

Let $M_\lambda = U(\mathfrak g)c_\lambda$ be the space of smooth functions on $G$ spanned by the iterated right derivatives of $c_\lambda$ (`New.HCParam.DsModule`). It is a module for $\mathfrak{gl}_n(\mathbb C)$ (`New.HCParam.dsAction`). Classically, for $c_\lambda(g) = \langle\pi(g)v, v\rangle$, the map $u \mapsto \langle\pi(\cdot)u, v\rangle$ takes $U(\mathfrak g)v$ onto this space. The source builds the space from $c_\lambda$ alone.

**Definition.** Let $\rho$ be a $\mathfrak{gl}_n(\mathbb C)$-module and $\nu$ an integer vector. A vector $x$ is *$K$-highest of weight $\nu$* for the parameter $l$ if $E_{aa}x = \nu_a x$ for every $a$, and $E_{ab}x = 0$ whenever $\varepsilon_a = \varepsilon_b$ and $l_b < l_a$. The vector $0$ is allowed.

Lean: `New.HCParam.IsKHighest` (Lib/DiscreteSeries/Rigidity/RepresentationsAndCasimirs.lean).

**Theorem.** If $l$ has gap $h$, then $c_\lambda$ is $K$-highest of weight $\Lambda$ in $M_\lambda$.

Lean: `New.isKHighest_dsGenerator`, `New.HCParam.DsModule` (Lib/DiscreteSeries/FlenstedJensen/SquareIntegrability.lean).

*Proof.* On $G$, $c_\lambda(g) = c_{-\lambda}(g^{-1})$ by the two symmetries of Section 4. The function $F(y) = c_{-\lambda}(y^{-1})$ is holomorphic near $G$, and for block diagonal $x$ that is upper triangular in the order of decreasing $l$, $F(gx) = x_{11}^{\Lambda_1}\cdots x_{nn}^{\Lambda_n}F(g)$ (`New.dsCoeff_neg_mul_borel_inv`). Differentiate in $x$ at $x = 1$. $\square$

**Definition.** Let $H$ be a $\mathfrak{gl}_n(\mathbb C)$-module with an inner product. It is *unitary with Casimir at least $\kappa_\lambda$* if $\langle E_{ab}v, w\rangle = \varepsilon_a\varepsilon_b\langle v, E_{ba}w\rangle$ for all $a, b, v, w$, and $\kappa_\lambda\|y\|^2 \le \operatorname{Re}\langle y, \Omega y\rangle$ for all $y$.

Lean: `New.IsUnitaryCasimirGe` (Lib/DiscreteSeries/Rigidity/RepresentationsAndCasimirs.lean).

The first condition says that the real Lie algebra $\mathfrak u(\operatorname{diag}\varepsilon)$ acts by skew-adjoint operators: it is the infinitesimal form of a unitary representation of $G$.

**Theorem.** Let $n \ge 1$, and let $l$ have gap $500n^3 + A$. Give $M_\lambda$ the inner product of $L^2(G)$ multiplied by $d_\lambda$. Then $M_\lambda$ is unitary with Casimir at least $\kappa_\lambda$, the vector $c_\lambda$ has norm $1$, and $|f(g)| \le \|f\|$ for every $f \in M_\lambda$ and $g \in G$.

Lean: `New.HCParam.HasLargeGap.isUnitaryCasimirGe_dsAction` (Lib/DiscreteSeries/FlenstedJensen/SquareIntegrability.lean). The embedding $f \mapsto \sqrt{d_\lambda}f$ in $L^2(G)$ is `New.HCParam.HasLargeGap.toL2`.

*Proof.* Each $f \in M_\lambda$ is a smearing $f(g) = \int_G \beta(y^{-1})c_\lambda(gy)\,dy$ of $c_\lambda$ by a smooth function $\beta$ of compact support (`New.exists_smear_dsCoeffSmooth_eq`). So $f$ has the decay of $c_\lambda$ up to a constant, and it is square integrable. The right derivatives are the derivatives of the right regular representation on $L^2(G)$, which is unitary; this gives the first condition. The Casimir operator is central, so it acts on all of $M_\lambda$ by its eigenvalue $\kappa_\lambda$ on $c_\lambda$. Each $f$ is its own coefficient against $c_\lambda$: $f(g) = d_\lambda\langle \text{right translate of } f \text{ by } g, c_\lambda\rangle$ (`New.HCParam.HasLargeGap.inner_toL2_dsGenerator_rightRegularL2`). At $f = c_\lambda$ and $g = 1$ this gives $\|c_\lambda\| = 1$, and the Cauchy-Schwarz inequality gives $|f(g)| \le \|f\|$. $\square$

**Remark (Formalization).** The structure `IsUnitaryCasimirGe` records only the inequality $\kappa_\lambda\|y\|^2 \le \operatorname{Re}\langle y, \Omega y\rangle$, although $\Omega$ acts on $M_\lambda$ by exactly $\kappa_\lambda$. The inequality is the form that the rigidity theorem below needs. The source does not prove that the completion of $M_\lambda$ is an irreducible unitary representation of $G$. Classically it is the discrete series with parameter $\lambda$ of Section 2, but no statement of the source depends on this.

### The idempotent kernel

**Definition.** A function $e$ on a group with a measure is an *idempotent kernel* if it is continuous and integrable, $e(g^{-1}) = \overline{e(g)}$, $e(1) \ne 0$, and

$$\int e(z)\,e((zx)^{-1}y)\,dz = \frac{e(x^{-1})}{e(1)}\,e(y)\quad\text{for all } x, y.$$

Lean: `New.IsIdempotentKernel` (Lib/General/Measure/IdempotentKernel.lean).

**Theorem.** If $e$ is an idempotent kernel, then $\int e(z)\,e(z^{-1}y)\,dz = e(y)$ for all $y$, that is, $e * e = e$.

Lean: `New.IsIdempotentKernel.convolution_self` (Lib/General/Measure/IdempotentKernel.lean).

*Proof.* Take $x = 1$ in the definition. $\square$

**Theorem.** Let $n \ge 1$, and let $l$ have gap $500n^3 + A$. Then $e_\lambda$ is an idempotent kernel on $G$. There is a smooth function $\alpha$ of compact support on $G$ with $\int_G \alpha(x^{-1})\,e_\lambda(x^{-1}g)\,dx = e_\lambda(g)$ for all $g$.

Lean: `New.HCParam.HasLargeGap.isIdempotentKernel_dsKernel`, `New.HCParam.HasLargeGap.exists_bump_conv_dsKernel` (Lib/DiscreteSeries/Rigidity/KernelFixes.lean).

*Proof.* The convolution identity is Schur orthogonality with the points $y^{-1}$ and $x$, multiplied by $d_\lambda^2$. The integrability is the case $C = 0$ of the integrability of $e_\lambda(g)\|g\|^C$ for $C \le A + 1$ (`New.HCParam.HasLargeGap.integrable_dsKernel_mul_norm_pow`). For the second claim, $c_\lambda$ is a smearing of itself, $c_\lambda(g) = \int_G \alpha(y^{-1})c_\lambda(gy)\,dy$, by the smearing theorem used above. Evaluate at $g^{-1}$ and conjugate. $\square$

The second claim says $\beta * e_\lambda = e_\lambda$ with $\beta(x) = \alpha(x^{-1})$ smooth of compact support. So results about $\pi(f)$ for a function $f$ with $f * e_\lambda = e_\lambda$ apply to a function $f = \beta$ of compact support.

### Rigidity

The rigidity theorem replaces the classification of representations by their lowest $K$-type. It is stated for any representation with an invariant form.

**Definition.** A homomorphism $\pi$ from $U(J)$ to the bounded operators on a normed space $X$, with a bounded sesquilinear form $B$ on $X$, is a *unitary representation of growth $A$* if each orbit map $g \mapsto \pi(g)x$ is continuous, $B(\pi(g)x, \pi(g)y) = B(x, y)$, $\overline{B(x,y)} = B(y,x)$, $\operatorname{Re}B(x,x) > 0$ for $x \ne 0$, and $\|\pi(g)\| \le c\|g\|^A$ for some constant $c$.

Lean: `New.IsUnitaryRep` (Lib/DiscreteSeries/Rigidity/RepresentationsAndCasimirs.lean).

The form $B$ need not give the topology of $X$. This is the case of interest: $X$ is a space of functions with a sup norm, and $B$ is a Petersson inner product.

**Definition.** A $\mathfrak{gl}_n$-module $\rho$ on a space $M$ is the *derivative* of $\pi$ along a linear map $\iota : M \to X$ if $\frac{d}{dt}\pi(\exp tY)\,\iota v\,\big|_{t=0} = \iota(\rho(Y)v)$ for all $Y$ in the Lie algebra of $U(J)$ and all $v \in M$.

Lean: `New.IsDerivedAction` (Lib/DiscreteSeries/Rigidity/RepresentationsAndCasimirs.lean).

**Theorem (Rigidity).** Let $n \ge 1$ and let $l = 2\lambda$ have gap $500n^3 + A$. Let $(\pi, B)$ be a unitary representation of $G$ of growth $A$ on $X$, and let $\rho$ be its derivative along $\iota : M \to X$. Let $v \in M$ be $K$-highest of weight $\Lambda$ for $\rho$, with $\iota(\Omega v) = c\,\iota v$ for a real number $c \ge \kappa_\lambda$. Then for every $g \in G$,

$$B(\iota v, \pi(g)\iota v) = B(\iota v, \iota v)\,c_\lambda(g).$$

Lean: `New.coeff_eq_dsCoeff_of_isKHighest` (Lib/DiscreteSeries/Rigidity/KernelFixes.lean).

The source calls this a variant of Parthasarathy's criterion, which recognises a discrete series by its lowest $K$-type. Here the Casimir bound replaces the condition that no $K$-type $\Lambda - \alpha$ occurs, and the conclusion is an equality of coefficients.

*Proof.* Let $H$ be the inner product space of $B$, and $x$ the image of $\iota v$. Let $H_x$ be the module generated by $x$. The Casimir bound and the invariance make $H_x$ unitary with Casimir at least $\kappa_\lambda$ (`New.exists_isUnitaryCasimirGe_generatedModule`). Form the orthogonal sum $H_x \oplus M_\lambda$. For each $t \in \mathbb C$ the vector $d(t) = (x, t\,c_\lambda)$ is $K$-highest of weight $\Lambda$. The vector $d(-\langle x, x\rangle)$ is orthogonal to $d(1)$, since $\|c_\lambda\| = 1$. A highest vector is orthogonal to the vectors that lowering operators produce from another highest vector, and the Casimir bound spreads the orthogonality to the whole module generated by $d(1)$ (`New.mem_orthogonal_filtration_of_casimirK`). Now consider, for each $g$, the linear form $(\iota u, f) \mapsto B(\iota v, \pi(g)\iota u) - \langle x, x\rangle f(g)$. It is bounded, it satisfies the differential equation of a coefficient map, and at $g = 1$ it is the inner product with $d(-\langle x, x\rangle)$. So at $g = 1$ it vanishes on the module generated by $d(1)$. A coefficient map that vanishes at $1$ on such a module vanishes at every $g$ on $d(1)$ (`New.HCParam.IsKHighest.coeffMap_eq_zero`), by analyticity of the coefficients. At $d(1)$ the form is $B(\iota v, \pi(g)\iota v) - B(\iota v, \iota v)c_\lambda(g)$. $\square$

**Remark (Formalization).** The vector $v = 0$ is allowed, and then the statement is $0 = 0$. The theorem does not say that a $K$-highest vector exists. The growth exponent of $\pi$ is the same number $A$ as in the gap: a larger gap allows representations of faster growth. The later volumes apply the theorem to spaces of automorphic forms with the sup norm and the Petersson form. Its main use is `New.integratedRep_fix_of_isKHighest`: if $f * e_\lambda = e_\lambda$, then $\pi(f) = \int f(g)\pi(g)\,dg$ fixes $\iota v$.

### Harish-Chandra's formula

The formal degree of Section 2 is $d_\pi = \dim V_{\lambda - \rho}$ for the measure compatible with the measure of mass $1$ on $U(n)$ (Harish-Chandra; the source cites Acta Math. 116 (1966), Theorem 16, and Knapp, *Representation Theory of Semisimple Groups* (1986), Theorem 12.7). Section 3 showed that the measure of the source is this compatible measure.

**Theorem (Weyl's dimension formula).** Let all signs be $1$, so that $K = G = U(n)$, and let $l = 2\lambda$ have some gap. Then $\Lambda = \lambda - \rho$, and $\big(\int_{U(n)}|m_\Lambda(k)|^2dk\big)^{-1} = \dim_\lambda$.

Lean: `New.weyl_dimension_formula` (Lib/DiscreteSeries/Character/WeylCharacterFormula.lean).

By Schur orthogonality for $U(n)$, the left side is the dimension of the representation of highest weight $\lambda - \rho$, and $\dim_\lambda = \prod_{\lambda_j < \lambda_i}(\lambda_i - \lambda_j)/\prod_{k<n}k!$ is Weyl's formula for it. The source proves the identity by comparing the denominator formula and the character formula along two one-parameter subgroups of the torus.

For a vector $\nu$ let $\chi_\nu(g) = \int_K m_\nu(y^{-1}gy)\,dy\,/\int_K|m_\nu|^2$ on $K$ (`New.HCParam.kTypeChar`). For $\nu$ dominant it is the character of the $K$-type of highest weight $\nu$ (`New.Orbital.weyl_character_kTypeChar`). Let $l^c$ be the vector $l$ with all signs $1$ (`New.HCParam.compactForm`). Its lowest $K$-type is $\lambda - \rho$, and $\chi$ for it is the character of $U(n)$ of highest weight $\lambda - \rho$.

**Theorem (Harish-Chandra's formula, the source's form).** Let $n \ge 1$, and let $l = 2\lambda$ have gap $500n^3 + 10n^5$. Then:

1. $d_\lambda = \dim_\lambda$.
2. For every $x = (x_1, \dots, x_n)$ of distinct complex numbers of modulus $1$,
$$(-1)^{pq}\sum_{\sigma \in S_n}\int_G e_\lambda\big(g^{-1}\operatorname{diag}(x_{\sigma(1)}, \dots, x_{\sigma(n)})\,g\big)\,dg = \#\{\sigma : \varepsilon\circ\sigma = \varepsilon\}\cdot\overline{\chi^{U(n)}_{\lambda-\rho}(\operatorname{diag}x)},$$
where $p$ and $q$ are the numbers of signs $+1$ and $-1$, and $\chi^{U(n)}_{\lambda-\rho}$ is $\chi$ for $l^c$.

Lean: `New.Orbital.harish_chandra_degree_and_orbital`, `New.HCParam.kTypeChar` (Lib/DiscreteSeries/Character/FormalDegree.lean, Lib/DiscreteSeries/Character/WeylCharacterFormula.lean). Part 1 alone is `New.Orbital.formalDegree_eq_weylDimensionPoly`.

In Lean the sign is $(-1)$ to the number of pairs $(a, b)$ with $\varepsilon_a = 1$ and $\varepsilon_b = -1$ (`New.Orbital.oppositePairs`), which is $pq$. The number $\#\{\sigma : \varepsilon\circ\sigma = \varepsilon\} = p!\,q!$ is the order of the Weyl group of $K$. The integrals converge absolutely (`New.Orbital.integrable_dsCoeff_conj`).

Classically, Harish-Chandra expressed the orbital integrals of a discrete series coefficient at regular elliptic points by the character of the representation. The permutations in $S_n$ fall into cosets of the Weyl group of $K$, and the cosets correspond to the discrete series with the same infinitesimal character (Section 2). So the left side is a stable sum over this set of representations. On the compact torus the sum of their characters is $(-1)^{pq}$ times the character of the finite dimensional representation with the same infinitesimal character, by the character formula of Section 2. The source proves only the stable sum, not the formula for each orbital integral.

*Proof.* The idea is to compute one Laurent polynomial in two ways. Let $D$ be the product of the noncompact roots $x_a - x_b$ on the torus, and $N = 4n^2$. By the decay of $c_\lambda$, $\Theta(x) = d_\lambda\int_G c_\lambda(g^{-1}\operatorname{diag}(x)g)\,dg$ times $D^{N+1}$ and the product of the compact roots is a Laurent polynomial $P$ in $x$ (`New.Orbital.exists_laurent_orbital_integral`). The *level* of a monomial is its pairing with an order opposite to $l$. A comparison with Harish-Chandra's character formula, monomial by monomial at low level (`New.Orbital.orbital_eq_char_sub_offOrbitIntegral`, `New.Orbital.coeff_eq_zero_of_low_level`), shows that $P$ is a scalar times $D^N$ times the alternant over the Weyl group of $K$ with the exponent of Weyl's numerator. The coefficient at the top monomial gives the scalar. Its absolute value is $d_\lambda\int_{U(n)}|m_{\lambda-\rho}|^2$, and its value is $1$. With Weyl's dimension formula, this gives Part 1. For Part 2, divide by $D^N$, conjugate, multiply by the Weyl denominator and sum over $S_n$; the sum of the alternants over $S_n$ is $p!\,q!$ times the full alternant, and Weyl's character formula for $U(n)$ identifies the result. $\square$

**Example.** In $U(1,1)$, $\dim_\lambda = k - 1$ by Section 3, and $\int_G|c_\lambda|^2 = \int_0^\infty \cosh^{-2k}t\,\sinh 2t\,dt = 1/(k-1)$ for the measure of Section 2. So $d_\lambda = k - 1$, as Part 1 says. Here $pq = 1$ and $p!\,q! = 1$, and $\lambda - \rho = (w_1 + 1, w_2 - 1)$. Part 2 says that minus the sum of the two orbital integrals of $e_\lambda$ at $\operatorname{diag}(x_1, x_2)$ and $\operatorname{diag}(x_2, x_1)$ is the conjugate of the character of the representation of $U(2)$ with highest weight $(w_2 - 1, w_1 + 1)$, of dimension $k - 1$.

**Remark (Formalization).** The theorem needs gap $500n^3 + 10n^5$, much more than the other results of this section, which hold for $500n^3 + A$ with any $A$. The source uses the extra size only in the proof of this theorem, in the Laurent polynomial property and the comparison of monomials of low level. The theorem is stated for the measure `volume` of $G$, which is the compact dual measure of Section 3. A different normalisation of the Haar measure would change $d_\lambda$ by a constant and break Part 1.
