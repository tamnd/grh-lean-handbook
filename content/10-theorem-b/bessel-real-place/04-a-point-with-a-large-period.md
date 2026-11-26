---
title: A point with a large period
lean:
  - New/Spanning/Bessel/LargeFunction.lean
decls:
  - New.DiscreteSeries.exists_sub_one_mul_frameCols_eq
  - New.DiscreteSeries.exists_sub_one_mul_definiteCols_eq
  - New.DiscreteSeries.exists_besselGraph_fst_eq
  - New.DiscreteSeries.besselPairHom
  - New.DiscreteSeries.isProperMap_besselPairHom_fst
  - New.DiscreteSeries.subOnePair_besselPairHom_fst
  - New.DiscreteSeries.norm_frame_mulVec_le
  - New.DiscreteSeries.IsPosition.exists_mul_eq_frameCols_and_besselLength_le
  - New.DiscreteSeries.initCols_eq_of_frame
  - New.DiscreteSeries.lowersFlag_besselPairHom
  - New.DiscreteSeries.inducesOn_besselPairHom
  - New.DiscreteSeries.exists_besselPairHom_fst_eq
  - New.DiscreteSeries.mul_sqrt_mul_pow_le_pow
  - New.DiscreteSeries.IsSteep.exists_stationary_point
  - New.DiscreteSeries.besselBallVolume_le_of_period
status: drafted
drafted_by: writer@claude-opus-5-5
---
## A point with a large period

By [the previous section](/chapter/bessel-real-place/#bessel-functions-as-averages), $d_\lambda\|W_x\|_2^2$ is the period $\langle v, W_x(x)\rangle$. The cut of a later section multiplies $W_x$ by a constant to make $\|W\|_2^2 = |I|$, and that constant is large if $\|W_x\|_2$ is small. The decay bounds of $W_x$ are in units of $\operatorname{vol}_x$. So the chapter needs a point $x$ at which the period is not small compared with $\operatorname{vol}_x$, and the length of $x$ must be bounded, since the cut is a cut in the length. This section finds such a point. The tool is Laplace's method of [the chapter on Laplace's method](/chapter/laplace-method/) in Volume 5, applied to the group $x^{-1}Rx$.

### The group R lowers the flag

The Laplace method of Volume 5 applies to the group of a position: the elements $g$ of $U(\varepsilon)$ such that $g - 1$ maps the span of the first $j$ vectors of a sequence $v_1, \dots, v_n$ into the span of the first $j - 1$ (`LowersFlag`, [the section on positions](/chapter/laplace-method/#positions-and-the-stationary-position)). The first step is to see that $R$ is such a group for the frame. Let $F$ be the $r \times n$ matrix with the columns $f_0, \dots, f_\varrho$, let $E$ be the matrix with the columns $e_0, \dots, e_{\varrho-1}$, and let $D$ be the matrix with the columns $x_i$.

**Lemma.** Let $s = (g, h) \in R$.

1. $(g - 1)F = EN$ for a $\varrho \times n$ matrix $N$ with $N_{ab} = 0$ for $b \leq a$, and $\sum_a N_{a, a+1} = \sigma(g)$.
2. $(g - 1)D = D(h - 1) + EC$ for a matrix $C$.
3. Conversely, if $g \in G_1$ and $(g - 1)F = EN$ with $N$ as in item 1, then $g$ is the first component of an element of $R$.

Lean: `New.DiscreteSeries.exists_sub_one_mul_frameCols_eq`, `New.DiscreteSeries.exists_sub_one_mul_definiteCols_eq`, `New.DiscreteSeries.exists_besselGraph_fst_eq` (New/Spanning/Bessel/LargeFunction.lean).

*Proof.* (1) and (2): write $s = \iota(h)u$ with $u \in \mathsf U$. The factor $\iota(h)$ fixes the frame and acts by $h$ on $X_0$. The factor $u$ is unitriangular on the frame, so $u - 1$ maps $f_b$ into the span of the $e_a$ with $a < b$. The block of $u$ from $X_0$ to the $e_a$ is $C$. The sum of the entries just above the diagonal on the frame is $\sigma(u) = \sigma(g)$. (3) The hypothesis says that $g$ fixes each $f_b$ modulo the earlier frame vectors, so $g \in S$. Write $g = u\iota(h)$; then $(g, h) \in R$. $\square$

### The pair homomorphism

**Definition.** For $x \in G_1$, the homomorphism $j_x : R \to U(\operatorname{diag}\varepsilon) \times U(k)$ sends $s = (g, h)$ to $(p^{-1}x^{-1}gxp, h)$, the first component being read in the sign frame $p$.

Lean: `New.DiscreteSeries.besselPairHom` (New/Spanning/Bessel/LargeFunction.lean).

**Lemma.** The first component of $j_x$ is proper, and its value minus one is the conjugate $(xp)^{-1}(g - 1)(xp)$.

Lean: `New.DiscreteSeries.isProperMap_besselPairHom_fst`, `New.DiscreteSeries.subOnePair_besselPairHom_fst` (New/Spanning/Bessel/LargeFunction.lean).

*Proof.* $R$ is closed in $G_1 \times U(k)$, and the projection $G_1 \times U(k) \to G_1$ is proper because $U(k)$ is compact. Conjugation is a homeomorphism. The second claim is the definition. $\square$

### A point that carries a position to the frame

Volume 5 gives a stationary position $(v, i_0)$ in $U(\operatorname{diag}\varepsilon)$: independent vectors $v_1, \dots, v_n$ and an isometry $i_0$ of $X_0$ into their orthogonal complement, with prescribed Gram matrix and with entries bounded by $(3B + a)^{2n}$ ([Theorem](/decl/New.DiscreteSeries.IsSteep.exists_isStationary/)). The next lemma moves this position to the standard frame of $G_1$ and bounds the length of the point that does it.

**Lemma (Length of the moving point).** Let $(v, i_0)$ be a position in $U(\operatorname{diag}\varepsilon)$ with $\langle v_n, v_n\rangle_\varepsilon = -1$. Let $M \geq 1$, and let $w_0, \dots, w_{2\varrho}$ be vectors with $w_a = v_{a+1}$ for $a \leq \varrho$, entries of modulus at most $M$, and $\langle w_a, w_c\rangle_\varepsilon = -1$ if $a + c = 2\varrho$ and $0$ if $a + c < 2\varrho$. Then there is $x \in G_1$ such that $xp$ carries $i_0$ to $D$ and $v$ to $F$, and
$$\ell(x) \leq 8n\sqrt r\,M.$$

Lean: `New.DiscreteSeries.IsPosition.exists_mul_eq_frameCols_and_besselLength_le`, with `New.DiscreteSeries.norm_frame_mulVec_le` (New/Spanning/Bessel/LargeFunction.lean).

*Proof.* The families $p(i_0, v)$ and $(D, F)$ are independent and have the same Gram matrix for $J_1$: the identity on $X_0$, zero between $X_0$ and the frame, and on the frame the Gram matrix of $f_0, \dots, f_\varrho$, which is $0$ except for $h(z, z) = -1$. Witt's theorem gives $x \in G_1$ with $x\,p(i_0, v) = (D, F)$. Then $x^{-1}f_a = p\,w_a$ for $a \leq \varrho$. The vectors $V_a = p\,w_a$ have length at most $\sqrt r\,M$, since $p$ is unitary and each $w_a$ has $r$ entries of modulus at most $M$, and their products for $J_1$ are those of the $w_a$ for $\operatorname{diag}\varepsilon$. So the bounded dual lemma of [the section on the length](/chapter/bessel-real-place/#the-group-the-bessel-subgroup-and-the-length) applies with $\sqrt r\,M$ in place of $M$, and gives $\ell(x) \leq 8(\varrho + 1)\sqrt r\,M$. $\square$

In the source the vectors $w_a$ for $a > \varrho$ are $\mu^{a-\varrho}v_1$, where $\mu$ is the weight of the lowest $K$-type of $l$ as a diagonal matrix. The Gram identities for them are part of the definition of a stationary position.

**Lemma.** Let $x$ be as in the previous lemma.

1. The first $\varrho$ columns of $v$ are $(xp)^{-1}E$.
2. For $s \in R$, the first component of $j_x(s)$ minus one lowers the flag of $v$ with the sum $\sigma(s)$, and it induces the second component minus one on the image of $i_0$.
3. Every element of the group of the position $v$ is the first component of $j_x(s)$ for some $s \in R$.

Lean: `New.DiscreteSeries.initCols_eq_of_frame`, `New.DiscreteSeries.lowersFlag_besselPairHom`, `New.DiscreteSeries.inducesOn_besselPairHom`, `New.DiscreteSeries.exists_besselPairHom_fst_eq` (New/Spanning/Bessel/LargeFunction.lean).

*Proof.* Conjugate the lemma on $R$ by $xp$. For item 3, take $g$ in the group of the position, put $g_1 = x\,pgp^{-1}x^{-1}$, check that $g_1 - 1$ lowers the flag of the frame, and apply item 3 of that lemma. $\square$

So $j_x$ satisfies the hypotheses of [Theorem](/decl/New.DiscreteSeries.IsStationary.period_lower_bound_of_surjective/), the version of Laplace's method for a group that maps onto the group of a position.

### The stationary point

**Lemma.** If $1 \leq B$, $3B + a \leq b^2$ and $8nr \leq b$, then $8n\sqrt r\,(3B + a)^{2\varrho + 2} \leq b^{5n}$.

Lean: `New.DiscreteSeries.mul_sqrt_mul_pow_le_pow` (New/Spanning/Bessel/LargeFunction.lean).

*Proof.* $\sqrt r \leq r$ and $(3B + a)^{2\varrho+2} \leq b^{4n}$, so the left side is at most $8nr\,b^{4n} \leq b^{4n+1} \leq b^{5n}$, as $b \geq 1$. $\square$

**Theorem (A point with a large period).** Let $l$ be steep for $(B, e)$ ([Definition](/decl/New.DiscreteSeries.IsSteep/)), with $2n$ coordinates outside a set $X$. Let $u$ be a parameter of $H = U(k)$ whose lowest $K$-type has the weight $a$ at one coordinate and $0$ on $X$. Let both parameters have entries of modulus at most $L$ and the large gap with excess $A$. Assume
$$1 \leq B,\quad 3B + a \leq b^2,\quad 8nr \leq b,\quad 10^{12} \leq \beta,\quad r + k + L \leq \beta,\quad 10^{30}\bigl((r + k)^2\log\beta\bigr)^3 \leq A.$$
Then there is $x \in G_1$ with $\ell(x) \leq b^{5n}$ and
$$\operatorname{meas}\{s \in R : \|x^{-1}sx - 1\| \leq 1\} \leq \beta^{20(r+k)^2}\Bigl|\int_R c_l(x^{-1}sx)\,\overline{c_u(h)}\,e^{\overline{\sigma(s)} - \sigma(s)}\,ds\Bigr|.$$

Lean: `New.DiscreteSeries.IsSteep.exists_stationary_point` (New/Spanning/Bessel/LargeFunction.lean).

*Proof.* The theorem on stationary positions gives a position $(v, i_0)$ with $n$ vectors, $\langle v_n, v_n\rangle = -1$, and entries of $v_1, \mu^c v_1$ bounded by $(3B + a)^{2n}$. The lemma on the moving point gives $x$ with $\ell(x) \leq 8n\sqrt r\,(3B + a)^{2\varrho+2}$, and the size lemma bounds this by $b^{5n}$. The lemma on $j_x$ shows that Laplace's method applies to $j_x$ with $\sigma$ as the phase. It bounds the measure of the set of $s$ where both components of $j_x(s)$ have norm at most $\beta + 1$ by the right side. That set contains the ball $\|x^{-1}sx - 1\| \leq 1$: there $\|x^{-1}sx\| \leq 2 \leq \beta + 1$, and $\|h\| = 1$ since $h$ is unitary. $\square$

**Remark (Formalization).** The docstring of `New.besselLength` that the source repeats in the docstring of this theorem describes the length as an infimum over $s$ in $R$. The definition takes the infimum over $S$. The two agree, since $R$ maps onto $S$, so this is a difference of wording only.

### From the period to the norm

**Theorem.** Let $\rho$ be continuous, $l$ of large gap, $v$ a vector with $\langle v, \rho(h)v\rangle = c_u(h)$ for all $h \in H$, and $P \geq 0$. If the measure of the ball is at most $P$ times the modulus of the period, as in the conclusion of the previous theorem, then
$$\operatorname{vol}_x \leq P\,d_\lambda\int_{\mathsf U\backslash G_1}\|W_x\|^2.$$

Lean: `New.DiscreteSeries.besselBallVolume_le_of_period` (New/Spanning/Bessel/LargeFunction.lean).

*Proof.* Since $\overline{c_u(h)} = \overline{\langle v, \rho(h)v\rangle} = \langle v, \rho(h)^{-1}v\rangle$, the period is $\int_R c_\lambda(x^{-1}sx)\langle v, \pi(s)^{-1}v\rangle\,ds = \langle v, W_x(x)\rangle$. By the norm identity of the previous section it equals $d_\lambda\|W_x\|_2^2$, which is real and nonnegative. The set of the hypothesis is the ball of $\operatorname{vol}_x$, by the definition of the pair $(g - 1, g' - 1)$. $\square$

The hypothesis on $v$ says that the matrix coefficient of $v$ under $\rho$ is the coefficient $c_u$ of the parameter $u$ of the compact group $H$. In the last section $\rho$ comes from a unitary Schur representation, and $v$ is chosen so that this holds.

**Example.** For the data $D$ the source takes $\beta = b^3$ and $A = r^7$. Then the theorem gives $\operatorname{vol}_x \leq b^{60(r+k)^2}d_\lambda\|W_x\|_2^2$. This is the input $m = 60(r + k)^2$ of the cut lemma of [the next section](/chapter/bessel-real-place/#decay-and-the-cut), whose hypothesis is $m + 99r^2 \leq 400r^2$. The inequality is $3 \cdot 20(r + k)^2 + 99r^2 \leq 400r^2$ (`New.Data.exponent_add_le_mul_sq_r`). It holds because $k \leq r$, so $60(r + k)^2 \leq 240r^2$.
