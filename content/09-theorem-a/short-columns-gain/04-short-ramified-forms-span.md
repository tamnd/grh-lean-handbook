---
title: Short ramified forms span
lean:
  - New/UpperBound/Size/ShortColumns.lean
decls:
  - New.span_setOf_mem_eq_top_of_eq_range
  - New.Data.sum_height_mul_columnCount_le
  - New.Data.isShort_ramifyingOp
  - New.Data.span_isShort_eq_top
  - New.Data.span_isShort_ramifiedSourceForms_eq_top
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Short ramified forms span

This section joins Sections 2 and 3. First the general theorem of Section 2 is applied to the source forms, with the bound $B = \exp(\mathrm{err}_0)/4^f$. Then the operator $R_{\Pi_N} = \prod_w(1 - z_w)$ carries these short forms onto a spanning set of $\mathrm{src}$, and it multiplies the bound by at most $4^f$. Here $\mathrm{err}_0 = f a \log^3 b$ is the error unit of [the data and its sizes](/chapter/data-and-sizes/), Section 6.

### Background for the spanning theorem

1. The rank of $X_0$ is $n_0 = k$ ([the data and its sizes](/chapter/data-and-sizes/), Section 3).
2. The column counts of the source weight are $c_\tau(1) = a$ at the $a$-places and $0$ elsewhere, $c_\tau(h) = 0$ for $1 < h < k$, and the other counts are at heights $h \ge k$ ([the objects of the upper bound](/chapter/upper-bound-objects/), Section 3).
3. The natural number $q_1 d$ lies in the different of $E$ ([CM fields](/chapter/cm-fields/), Section 7).
4. The constant of short bases is $C(N) = 6N(f|n|)^2$ ([reduction theory](/chapter/reduction-theory/), Section 5).

### A spanning lemma

**Lemma.** Let $S$ span a complex vector space $V$, let $F$ be a linear map of $V$ with image $W$, and let $T \subseteq V$ with $F(S) \subseteq T$. Then the elements of $W$ that lie in $T$ span $W$.

Lean: `New.span_setOf_mem_eq_top_of_eq_range` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* The map $F$, read as a map onto $W$, is onto. A linear map sends a span to the span of the image, so $F(S)$ spans $W$. Each element of $F(S)$ lies in $W$ and in $T$. $\square$

### Short source forms span

The general theorem of Section 2 needs a bound $M$ for $|n| f + \mathrm{boxes}(c, |n|)$ with $|n| = k$.

**Lemma.** At every infinite place $\tau$, $\sum_{h < k} h\,c_\tau(h) \le a$.

Lean: `New.Data.sum_height_mul_columnCount_le` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* By fact 1 the heights below the rank are the $h < k$. By fact 2 the only nonzero term with $h < k$ is $h = 1$, and it is $c_\tau(1) \le a$. $\square$

So $\mathrm{boxes}(c, k) \le f a$, and $M = kf + fa$ works.

**Theorem (Short source forms span).** The source forms that are $\exp(\mathrm{err}_0)/4^f$-short span $\mathcal F$.

Lean: `New.Data.span_isShort_eq_top` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* Apply the theorem that short forms span (Section 2) to the level $K_0$, the weight $(c, e_0)$ and the number $N_E = q_1 d$. The hypotheses hold as follows.

1. The index set $X_0$ is nonempty and has $k$ elements.
2. The level $K_0$ is free ([the objects of the upper bound](/chapter/upper-bound-objects/), Section 7).
3. The number $q_1 d$ is nonzero and lies in the different, by fact 3.
4. $M = kf + fa \ge kf + \mathrm{boxes}(c, k)$, by the previous lemma.
5. The constant is $C(q_1 d) = 6q_1 d(fk)^2$, by fact 4. The table of sizes gives
$$\log\Bigl(4^f\bigl(6q_1d(fk)^2\bigr)^{6(kf + fa)}\Bigr) \le \mathrm{err}_0.$$
So $C(q_1d)^{6M} \le \exp(\mathrm{err}_0)/4^f$.

The theorem of Section 2 gives the claim. $\square$

**Remark (Formalization).** The size bound in step 5 is one call to `le_of_hasLogBound`, followed by `Real.le_exp_of_log_le`. The reason it holds is this. The base is $6q_1d(fk)^2 \le x^{50}$, by the rows of the table for $q_1$, $f$ and $k$, and by $d \le C_P \le x$. So its logarithm is at most $50\log x$, which is at most $\log b$, since $\log b \ge (\log x_1)^6 \ge (10^6\log x)^6$. The exponent is $6(kf + fa) \le 12 f a$, since $k \le a$. The factor $4^f$ adds $f\log 4$. The total is at most $12fa\log b + f\log 4$, which is far below $f a\log^3 b$.

### The operator keeps forms short

**Lemma (Ramifying a short form).** Let $s \subseteq \Pi_N$ and let $\varphi$ be a $B$-short source form. Then $R_s\varphi$ is $4^{|s|}B$-short.

Lean: `New.Data.isShort_ramifyingOp` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* Induction on $s$. For $s = \emptyset$, $R_\emptyset\varphi = \varphi$. For $w \notin s$, $R_{s\cup\{w\}}\varphi = \psi - z_w\psi$ with $\psi = R_s\varphi$, and $\psi$ is $4^{|s|}B$-short by induction. The operator $z_w$ is right translation by the scalar matrix $z_w1$. That matrix lies in the maximal compact subgroup at $w$ (Section 3), so it has integral entries. The lemma on translates (Section 2) shows that $\psi - z_w\psi$ is $4\cdot 4^{|s|}B$-short. $\square$

### The theorem on ramified forms

**Theorem (Short ramified source forms).** The ramified source forms that are $\exp(\mathrm{err}_0)$-short span $\mathrm{src}$.

Lean: `New.Data.span_isShort_ramifiedSourceForms_eq_top` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* Put $Z = \exp(\mathrm{err}_0)/4^f$. Let $S$ be the set of $Z$-short source forms and $T$ the set of $\exp(\mathrm{err}_0)$-short source forms. By the theorem that short source forms span, $S$ spans $\mathcal F$. The set $\Pi_N$ has $f$ elements, so by the previous lemma $R_{\Pi_N}$ maps $S$ into the $4^fZ$-short forms, and $4^fZ = \exp(\mathrm{err}_0)$. So $R_{\Pi_N}(S) \subseteq T$. By the theorem that the ramified forms are an image (Section 3), $\mathrm{src}$ is the image of $R_{\Pi_N}$. The spanning lemma gives the claim. $\square$

The theorem is used in [the proof of Theorem A](/chapter/proof-of-theorem-a/). There the chain of lifts is evaluated on a basis of $\mathrm{src}$ made of short forms. Integrality at every $p$-adic place controls the denominators of the values, and the bound $\exp(\mathrm{err}_0)$ controls their archimedean size. The cost $\mathrm{err}_0 = f a\log^3 b$ is one error unit, which is small compared to the gain.

### Examples

**Example (The factor 4 is sharp).** The lemma on translates cannot give a factor less than $4$ in general. On source forms the operator $z_w$ has order dividing $N - 1$, which is even, so $-1$ can be an eigenvalue. Suppose that a $B$-short source form $\varphi$ satisfies $z_w\varphi = -\varphi$. Then $(1 - z_w)\varphi = 2\varphi$, and $\|2\varphi(g)\|_W^2 = 4\|\varphi(g)\|_W^2$. So if $\|\varphi(g)\|_W^2 = B$ at some $g$, the best bound for $(1 - z_w)\varphi$ is $4B$. Such a form is in the kernel of $\sum_{i<N-1}z_w^i$, since a sum of $(-1)^i$ over an even number of terms is $0$.

**Example (The bound $4^f$ against the triangle inequality).** Expand $R_{\Pi_N}\varphi = \sum_{s\subseteq\Pi_N}(-1)^{|s|}z_s\varphi$, where $z_s = \prod_{w\in s}z_w$. This is a sum of $2^f$ translates of $\varphi$. The triangle inequality gives $\|R_{\Pi_N}\varphi(g)\|_W \le 2^f\sqrt B$, so the squared norm is at most $4^fB$. The induction in the lemma on ramifying a short form gives the same bound. In the proof of Theorem A the cost is $\log 4^f = f\log 4$, which is much smaller than $\mathrm{err}_0$.

**Example (Sizes).** Compare the two sides of the size bound in step 5 as functions of the scales. The left side is about $6fa\cdot\log C(q_1d)$, and $\log C(q_1 d)$ is of the order of $\log x$. The right side is $fa\log^3 b$. Both sides have the factor $fa$, and the table gives $\log x \le (\log b)^{1/6}/10^6$. So the ratio of the two sides is at most about $(\log b)^{-17/6}$. The margin is not used. Only the shape $\mathrm{err}_0 = f a\log^3 b$ matters, since the errors of Theorem A are multiples of this unit.
