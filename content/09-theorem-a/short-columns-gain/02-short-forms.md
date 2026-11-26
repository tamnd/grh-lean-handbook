---
title: Short forms
lean:
  - New/UpperBound/Size/ShortColumns.lean
decls:
  - New.IsShort
  - New.IsShort.sub_translate
  - New.norm_weylEval_le_one_of_integral
  - New.weylRep_mul_weylRep_zero
  - New.norm_weylRep_mulVec_det_smul_weylEval_le_one
  - New.weylNormSq_det_smul_weylRep_mulVec_weylEval_le
  - New.isShort_deltaForm
  - New.span_isShort_eq_top
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Short forms

This section works on one unitary group, with no data. It defines short forms, shows that a difference of a form and its translate stays short, and proves that short forms span the forms of a free level. Section 4 applies the result to the source forms.

### Background for short forms

Let $E$ be a CM field with $f$ infinite places, let $n$ be a finite index set, and let $G_f$ be the unitary group of the standard form $\sum_i x_i\bar x_i$ over the finite adeles of $E$. A weight $(\kappa, e)$ gives at each infinite place $\tau$ a Young diagram with $\kappa_\tau(h)$ columns of height $h$, and a power $e_\tau \in \mathbb{Z}$ of the determinant. The following facts come from earlier volumes. Each is stated in one line.

1. The Weyl module of $\kappa$ has the coordinates $\mathbb{C}^I$, a family $g = (g_\tau)$ of invertible matrices acts on it in weight $(\kappa, e)$ by $\rho_{\kappa,e}(g) = \prod_\tau \det(g_\tau)^{e_\tau}\, S_\kappa(g)$, and $S_\kappa$ is the Schur matrix ([Weyl modules](/chapter/weyl-modules/), Section 4).
2. The evaluation vector $\mathrm{ev}_y$ of an array $y$ has as coordinates the values at $y$ of fixed polynomials with integer coefficients, the products of minors ([Weyl modules](/chapter/weyl-modules/), Section 4).
3. The squared Weyl norm $\|\xi\|_W^2 = \xi^* G \xi$ uses a positive definite Gram matrix $G$ with integer entries, so $\|t\xi\|_W^2 = |t|^2\|\xi\|_W^2$ ([Weyl modules](/chapter/weyl-modules/), Section 5).
4. For complex matrices $z_\tau$ there are numbers $\rho_{\tau,i} \ge 0$, $i < |n|$, with $\sum_i \rho_{\tau,i} \le \sum_{a,b}|z_\tau(a,b)|^2$ and $\|S_\kappa(z)\xi\|_W^2 \le \prod_{\tau,i}\rho_{\tau,i}^{\lambda(\tau,i)}\|\xi\|_W^2$, where $\lambda(\tau, i) = \sum_{i < h < |n|}\kappa_\tau(h)$ ([Weyl modules](/chapter/weyl-modules/), Section 6, `New.weylNormSq_schur_le`).
5. For a $p$-adic place $\iota : \mathbb{C} \to \mathbb{C}_p$ the gauge $\|\xi\|_g$ of $\xi$ at $g \in G_f$ is the largest absolute value of a coordinate of $\rho_{\kappa,e}(g^{-1})\iota(\xi)$, and a form $\varphi$ is integral at $\iota$ if $\|\varphi(g)\|_g \le 1$ for all $g$ ([automorphic forms](/chapter/automorphic-forms/), Section 9).
6. The gauge does not change under $g \mapsto gk$ for $k$ with integral entries, and the integral forms are a module over the valuation ring of $\iota$ ([automorphic forms](/chapter/automorphic-forms/), Section 9).
7. At a free level $K$, every form is the sum over the classes $c$ of the delta forms $\delta_{x_c, \varphi(x_c)}$, where $x_c$ represents $c$ ([automorphic forms](/chapter/automorphic-forms/), Section 6).
8. The gauge of a delta form satisfies $\|\delta_{x,v}(g)\|_g \le \|v\|_x$ ([automorphic forms](/chapter/automorphic-forms/), Section 9).
9. For $N \ne 0$ in the different of $E$ and $g \in G_f$ there is $Y \in \mathrm{GL}_n(E)$ with $g^{-1}Y$ integral and $|\phi(Y_{ij})| \le C(N) = 6N(fn)^2$ for every embedding $\phi : E \to \mathbb{C}$ ([reduction theory](/chapter/reduction-theory/), Section 5).

Three facts from the same library are not stated elsewhere in the book. The first is a norm bound for delta forms.

**Lemma (Norm of a delta form).** Let the character of the level have finite order. For every automorphism $\sigma$ of $\mathbb{C}$, every $x$ and $g$, $\|\sigma(\delta_{x,v}(g))\|_W^2 \le (\#\Gamma_x)^2\,\|\sigma(v)\|_W^2$, where $\Gamma_x$ is the finite group of rational points that fix the class of $x$.

Lean: `New.Rows.weylNormSq_deltaForm_le` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

The value $\delta_{x,v}(g)$ is a sum of at most $\#\Gamma_x$ vectors $\gamma^{-1}v$ times roots of unity, and $\gamma$ is unitary for the Weyl norm. The Cauchy inequality gives the square. The second fact is the ultrametric Schur bound.

**Lemma (Schur matrices over an ultrametric field).** Over an ultrametric normed field, if every entry of every $A_\tau$ has absolute value at most $1$, then $\|S_\kappa(A)v\| \le \|v\|$ for the largest absolute value of a coordinate.

Lean: `New.Rows.norm_schur_mulVec_le` (Lib/GLn/Dual.lean).

The entries of $S_\kappa(A)$ are polynomials with integer coefficients in the entries of $A$, so they lie in the valuation ring. The third fact says that evaluation vectors span.

**Lemma (Evaluation vectors span).** Two linear maps from the Weyl module into a free module over a domain $R$ agree if they agree on $\mathrm{ev}_y$ for every array $y$ whose entries lie in a fixed infinite set $s \subseteq R$ and at which a fixed product of powers of determinants does not vanish.

Lean: `New.GL.ext_weylEval` (Lib/GLn/SchurModule/WeylKernel.lean).

In this chapter the powers are all $0$, so the condition on the determinants is empty.

### Short forms and translates

**Definition (Short forms).** Let $B$ be real. An algebraic form $\varphi$ of weight $(\kappa, e)$ is *$B$-short* if two conditions hold. First, for every prime $p$ and every $p$-adic place $\iota$ of $\mathbb{C}$, the form is integral at $\iota$. Second, for every automorphism $\sigma$ of $\mathbb{C}$ and every $g \in G_f$, $\|\sigma(\varphi(g))\|_W^2 \le B$.

Lean: `New.IsShort` (New/UpperBound/Size/ShortColumns.lean).

**Remark (Formalization).** The first condition quantifies over the instances `[Fact p.Prime]` and `[PadicPlace p]`. An instance of `PadicPlace p` is a choice of a ring map $\iota_p : \mathbb{C} \to \mathbb{C}_p$, so the quantifier runs over all $p$-adic places. The automorphism $\sigma$ acts on the coordinates of $\varphi(g)$.

**Lemma (Translates).** Let $\varphi$ be $B$-short and let $k \in G_f$ have integral entries. Then $\varphi - k\varphi$ is $4B$-short, where $(k\varphi)(g) = \varphi(gk)$.

Lean: `New.IsShort.sub_translate` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* Integrality: $\|\varphi(gk)\|_g = \|\varphi(gk)\|_{gk} \le 1$ by fact 6, so $k\varphi$ is integral at $\iota$. The integral forms are a module, so $\varphi - k\varphi$ is integral at $\iota$. Norm: write $\alpha = \sigma(\varphi(g))$ and $\beta = \sigma(\varphi(gk))$. The squared Weyl norm is a hermitian form, so the parallelogram law holds:
$$\|\alpha - \beta\|_W^2 + \|\alpha + \beta\|_W^2 = 2\|\alpha\|_W^2 + 2\|\beta\|_W^2.$$
Both $\|\alpha\|_W^2$ and $\|\beta\|_W^2$ are at most $B$, and $\|\alpha + \beta\|_W^2 \ge 0$. So $\|\alpha - \beta\|_W^2 \le 4B$. $\square$

### Evaluation vectors that are integral and small

The next three lemmas make vectors that are integral at a given point and small at every complex place.

**Lemma.** Let $y$ be an array over $\mathbb{C}_p$ with entries of absolute value at most $1$. Then every coordinate of $\mathrm{ev}_y$ has absolute value at most $1$.

Lean: `New.norm_weylEval_le_one_of_integral` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* By fact 2 each coordinate is the value at $y$ of a polynomial with integer coefficients. The integers of $\mathbb{C}_p$ form a ring that contains $\mathbb{Z}$ and the entries of $y$. $\square$

**Lemma.** For families $G$ and $Z$ of invertible matrices over a commutative ring, $\rho_{\kappa,e}(G)\,\rho_{\kappa,0}(Z) = \prod_\tau \det(G_\tau)^{e_\tau}\, S_\kappa(GZ)$.

Lean: `New.weylRep_mul_weylRep_zero` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* By fact 1, $\rho_{\kappa,0}(Z) = S_\kappa(Z)$, and $S_\kappa$ is multiplicative. $\square$

**Lemma (Integral at g).** Let $g \in G_f$, let $Y_0$ and $Y_\tau$ be in $\mathrm{GL}_n(E)$, and suppose that $g^{-1}Y_0$ and $(g^{e_\tau})^{-1}Y_\tau$ have integral entries for every $\tau$. Let $y$ be an array over $\mathbb{C}_p$ with entries of absolute value at most $1$. Then
$$\Bigl\|\rho_{\kappa,e}(g^{-1})\Bigl(\prod_\tau \det(Y_\tau)\cdot \rho_{\kappa,0}(Y_0)\,\mathrm{ev}_y\Bigr)\Bigr\| \le 1.$$
Here $E$ maps to $\mathbb{C}_p$ by $\iota$ composed with $\tau$ at the place $\tau$, and the finite adeles by the extension of that map.

Lean: `New.norm_weylRep_mulVec_det_smul_weylEval_le_one` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* Put $d_\tau = \det(Y_\tau)\det(g^{-1})^{e_\tau} = \det((g^{e_\tau})^{-1}Y_\tau)$. It is the determinant of an integral matrix, so $|d_\tau| \le 1$. By the previous lemma the vector is $\prod_\tau d_\tau \cdot S_\kappa(g^{-1}Y_0)\,\mathrm{ev}_y$. The entries of $g^{-1}Y_0$ are integral adeles, and their images in $\mathbb{C}_p$ have absolute value at most $1$. By the ultrametric Schur bound and the first lemma, $\|S_\kappa(g^{-1}Y_0)\,\mathrm{ev}_y\| \le \|\mathrm{ev}_y\| \le 1$. The product of the $|d_\tau|$ is at most $1$. $\square$

The number of boxes of $\kappa$ below height $|n|$ is $\mathrm{boxes}(\kappa, |n|) = \sum_\tau\sum_{h < |n|} h\,\kappa_\tau(h)$.

**Lemma (Small at every complex place).** Let $n$ be nonempty. Let $R \ge |n|$, let $M \ge |n| f + \mathrm{boxes}(\kappa, |n|)$, and let $R^{6M} \le B$. Let $Y_0$ and $Y$ be families of invertible complex matrices with entries of absolute value at most $R$, and let $y$ be a complex array with entries of absolute value at most $1$. Then
$$\Bigl\|\prod_\tau \det(Y_\tau)\cdot \rho_{\kappa,0}(Y_0)\,\mathrm{ev}_y\Bigr\|_W^2 \le B.$$

Lean: `New.weylNormSq_det_smul_weylRep_mulVec_weylEval_le` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* Note $R \ge |n| \ge 1$. Let $y^\square_\tau$ be the square part of $y$ at $\tau$, the $n \times n$ matrix of the entries $y((\tau, a), b)$ with $b < |n|$. The library gives $\mathrm{ev}_y = S_\kappa(y^\square)\,u$, where $u$ is the evaluation vector of an array of zeros and ones with $\|u\|_W^2 = 1$ (`New.GL.schur_squarePart_mulVec`, `New.GL.weylNormSq_weylEval_permArray`). So $\rho_{\kappa,0}(Y_0)\,\mathrm{ev}_y = S_\kappa(z)\,u$ with $z_\tau = Y_{0,\tau}\,y^\square_\tau$.

Each entry of $z_\tau$ is a sum of $|n|$ products of absolute value at most $R$, so it is at most $|n|R$. Fact 4 gives numbers $\rho_{\tau,i}$ with
$$\rho_{\tau,i} \le \sum_{a,b}|z_\tau(a,b)|^2 \le |n|^2 (|n|R)^2 = |n|^4R^2 \le R^6.$$
The exponents $\lambda(\tau, i)$ add up over $(\tau, i)$ to $\mathrm{boxes}(\kappa, |n|)$, since a column of height $h$ counts once for each $i < h$. So $\|S_\kappa(z)u\|_W^2 \le (R^6)^{\mathrm{boxes}(\kappa,|n|)}$.

For the determinants, the operator norm of $Y_\tau$ is at most its Frobenius norm, which is at most $|n|R \le R^2$. So $|\det Y_\tau|^2 \le R^{4|n|} \le (R^6)^{|n|}$, and the product over the $f$ places is at most $(R^6)^{|n|f}$. By fact 3 the squared norm is at most $(R^6)^{|n|f + \mathrm{boxes}(\kappa,|n|)} \le R^{6M} \le B$. $\square$

### Short delta forms

A level $K$ is free if $\Gamma \cap gKg^{-1}$ is trivial for every $g$, where $\Gamma$ is the group of rational points.

**Lemma (Short delta forms).** Let $K$ be a free level, $x \in G_f$ and $v$ a coordinate vector. Suppose that $\|v\|_x \le 1$ for every $p$-adic place, and that $\|\sigma(v)\|_W^2 \le B$ for every automorphism $\sigma$ of $\mathbb{C}$. Then the delta form $\delta_{x,v}$ of level $K$ with trivial character is $B$-short.

Lean: `New.isShort_deltaForm` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* The trivial character has finite order. By fact 8, $\|\delta_{x,v}(g)\|_g \le \|v\|_x \le 1$. The level is free, so the group $\Gamma_x$ is trivial. The lemma on the norm of a delta form gives $\|\sigma(\delta_{x,v}(g))\|_W^2 \le 1^2\,\|\sigma(v)\|_W^2 \le B$. $\square$

### Short forms span

**Theorem (Short forms span).** Let $n$ be nonempty and let $K$ be a free level. Let $N \ne 0$ be a natural number in the different of $E$, and let $M \ge |n| f + \mathrm{boxes}(\kappa, |n|)$. If $C(N)^{6M} \le B$, with $C(N) = 6N(fn)^2$, then the $B$-short forms of level $K$ span the space of forms of level $K$.

Lean: `New.span_isShort_eq_top` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* Let $V$ be the span of the $B$-short forms. By fact 7 each form is a finite sum of delta forms $\delta_{x_c, w}$, one for each class $c$. So it is enough to show that $\delta_{x_c, w} \in V$ for every class $c$ and every vector $w$. Fix $c$ and write $x = x_c$.

For every $g$, fact 9 gives a matrix $Y(g)$ with $g^{-1}Y(g)$ integral and all conjugates of its entries at most $C(N)$. Put
$$A = \prod_\tau \det Y(x^{e_\tau}) \cdot \rho_{\kappa,0}(Y(x)),$$
where at the place $\tau$ the matrices are read through $\tau$. For a ring map $\phi$ from $\mathbb{C}$ to a normed field, write $A_\phi$ for the same matrix with $\phi$ applied to the entries. Then $\phi(A\,\mathrm{ev}_y) = A_\phi\,\mathrm{ev}_{\phi(y)}$, since the coordinates of $\mathrm{ev}_y$ are integer polynomials.

Let $y$ be an array whose entries are roots of unity. Then $|\phi(y_i)| = 1$ in every normed field. The vector $A\,\mathrm{ev}_y$ has two properties.

1. It is integral at $x$. For a $p$-adic place $\iota$, $\|A\,\mathrm{ev}_y\|_x$ is the norm of $\rho_{\kappa,e}(x^{-1})A_\iota\,\mathrm{ev}_{\iota(y)}$, and the lemma on integrality at $g$ applies with $Y_0 = Y(x)$ and $Y_\tau = Y(x^{e_\tau})$.
2. It is small. The number $|n|$ divides $C(N)$, so $|n| \le C(N)$. For an automorphism $\sigma$, the lemma on smallness applies to $A_\sigma\,\mathrm{ev}_{\sigma(y)}$ with $R = C(N)$, since every conjugate of an entry of $Y(g)$ is at most $C(N)$.

By the lemma on short delta forms, $\delta_{x, A\,\mathrm{ev}_y}$ is $B$-short. So the linear map
$$L : w \mapsto \delta_{x, Aw} \bmod V$$
from the Weyl module to the quotient by $V$ vanishes at every $\mathrm{ev}_y$ with entries in the set $s$ of roots of unity. The set $s$ is infinite: for every $k > 0$ the number $e^{2\pi i/k}$ has order $k$. The quotient is a vector space, so it is free. By the lemma that evaluation vectors span, $L = 0$.

The matrix $A$ is invertible: $\rho_{\kappa,0}$ is a group map, so $\rho_{\kappa,0}(Y(x))$ is a unit, and the determinants are nonzero. So $w \mapsto Aw$ is onto, and $\delta_{x, w} \bmod V = 0$ for every $w$. $\square$

**Remark (Formalization).** The short bases $Y(g)$ are taken with `choose` from `New.Space.exists_short_basis_stdSpace`. The statement of the theorem is a proposition, so the choice does not change it. The representatives $x_c$ are `Quot.out` of the classes. The source declares the theorem under `seal Finset.sum in`. This keeps the definitional checks from unfolding the finite sums; it changes no statement.

The constant of the theorem is large. For the source forms of Section 4, $C(N)^{6M}$ is about $\exp(6 f a \log C(N))$, and the table of sizes shows that it stays below $\exp(f a\log^3 b)/4^f$.
