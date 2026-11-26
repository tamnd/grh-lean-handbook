---
title: Decay and the cut
lean:
  - New/Spanning/Bessel/Basic.lean
  - New/Spanning/Bessel/CutTailBound.lean
decls:
  - New.FullOrCut
  - New.FullOrCut.select
  - New.IsDecayMajorant
  - New.IsCutPair
  - New.norm_frameEquiv
  - New.lintegral_formalDegree_mul_decay_le
  - New.formalDegree_mul_lintegral_decay_le
  - New.formalDegree_mul_volume_ball_le
  - New.besselLength_div_le_half_norm
  - New.scaledBesselLength_pow_mul_enorm_besselAverage_le
  - New.IsBesselFunction.smul_of_invariant
  - New.exists_enorm_sq_mul_eq
  - New.besselCutoff
  - New.besselCut
  - New.enorm_besselCut_le
  - New.enorm_besselCut_sub_le
  - New.inCut_of_besselCut_ne_zero
  - New.lt_besselLength_of_besselCut_ne
  - New.IsBesselFunction.besselCut
  - New.IsDecayMajorant.lintegral_sq_besselCut_sub_le
  - New.lintegral_besselGraph_mul_eq
  - New.exists_isDecayMajorant_besselAverage
  - New.exists_isCutPair_besselAverage
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Decay and the cut

This section turns the average $W_x$ into the pair $(W, W^\flat)$ of a Bessel system. The function $W$ is a real multiple $cW_x$ with $\|W\|_2^2 = |I|$. The function $W^\flat$ is $W$ times a cutoff in the length $\ell$. The section proves that the two functions decay fast in $\ell$, below one common majorant, and that $W^\flat$ is close to $W$ in $L^2(\mathsf U\backslash G_1)$. All integrals over $\mathsf U\backslash G_1$ are for the quotient measure. Throughout, $l$ has the gap $500r^3 + A$ and entries of modulus at most $L$, $M = 9r^2$, and $n = \varrho + 1$.

### The two structures

The source keeps the two functions in one family indexed by a type with two elements.

**Definition.** `FullOrCut` has the two elements `full` and `cut`. For two objects $W, W'$, the family $\operatorname{select}(W, W')$ is $W$ at `full` and $W'$ at `cut`.

Lean: `New.FullOrCut`, `New.FullOrCut.select` (New/Spanning/Bessel/Basic.lean).

**Definition (Decay majorant).** Let $b \in \mathbb{R}$, $f \in \mathbb{N}$, and let $W_t$, $t \in \{\text{full}, \text{cut}\}$, be two continuous functions. A function $A : G_1 \to [0, \infty]$ with a number $a \in [0, \infty]$ is a *decay majorant* if:

1. $A$ is measurable and left invariant under $S$;
2. $\ell_b(y)^{3r^3f}\,\|W_t(y)\| \leq A(y)$ for both $t$ and all $y$;
3. $A \leq a$ and $a < \infty$;
4. $a\int_{\mathsf U\backslash G_1} A \leq b^{400r^2}\,|I|$.

Lean: `New.IsDecayMajorant` (New/Spanning/Bessel/Basic.lean).

Here $\ell_b = \max(1, \ell/b^{6n})$ is the scaled length of [the section on the length](/chapter/bessel-real-place/#the-group-the-bessel-subgroup-and-the-length). Item 4 combines a sup bound and an $L^1$ bound. The product is what a bound for $\int A^2$ needs, since $\int A^2 \leq a\int A$.

**Definition (Cut pair).** A family $(W_t)$ is a *cut pair* for $b$, $f$ and $\rho$ if:

1. both $W_t$ are Bessel functions for $\rho$;
2. $W = W_{\text{full}}$ is integrable on $\mathsf U\backslash G_1$ and $\int\|W\|^2 = |I|$;
3. $W^\flat = W_{\text{cut}}$ has $\int\|W^\flat\|^2 \leq |I|$;
4. $W^\flat(y) \neq 0$ implies $\ell(y) \leq b^{6n+2}$;
5. $\int\|W^\flat - W\|^2 \leq b^{-2r^3f}\,|I|$;
6. $W^\flat(y) \neq W(y)$ implies $\ell(y) > b^{6n+2}/2$;
7. a decay majorant exists for $(W_t)$.

Lean: `New.IsCutPair` (New/Spanning/Bessel/Basic.lean).

**Remark (Formalization).** All integrals in the two structures are lower Lebesgue integrals in $[0, \infty]$. So item 2 says that the integral is finite and equal to $|I|$, with no separate statement of square integrability. The bound of item 5 is written as $\bigl(b^{-1}\bigr)^{r^3f}$ squared, and for $b \leq 0$ this has no meaning as a decay. The users of the structure have $b \geq 2000$.

### The tail of the coefficient on the whole group

**Lemma.** Let $b \geq 2000$ and $r + L + 1 \leq b^4$.

1. For $c > 8r^2$, $\int_{G_1} d_\lambda(2/\|g\|)^c\,dg \leq b^{50r^2+1}\,2^c$.
2. $d_\lambda \cdot \int_{G_1}(2/\|g\|)^M\,dg \cdot 16^M \leq b^{99r^2}$.
3. For $T \geq 1$, $d_\lambda\operatorname{vol}\{g : \|g\| \leq T\} \leq T^{9r^2}b^{99r^2}$.

Lean: `New.norm_frameEquiv`, `New.lintegral_formalDegree_mul_decay_le`, `New.formalDegree_mul_lintegral_decay_le`, `New.formalDegree_mul_volume_ball_le` (New/Spanning/Bessel/CutTailBound.lean).

*Proof.* (1) The tail bound of the discrete series (`New.integral_tail_le`, Lib/DiscreteSeries/FlenstedJensen/SquareIntegrability.lean) gives $8(2000(r + L + 1)^6)^{2r^2}2^c$ on $U(\operatorname{diag}\varepsilon)$. The unitary frame carries it to $G_1$ without a change of the norm. Then $8 \leq b$, $2000 \leq b$ and $r + L + 1 \leq b^4$ give $b \cdot (b \cdot b^{24})^{2r^2} = b^{50r^2+1}$. (2) Apply (1) with $c = M$. Then $2^M16^M \leq b^{2M}$, and $50r^2 + 1 + 18r^2 \leq 99r^2$. (3) Chebyshev: on the ball, $1 \leq (T/2)^M(2/\|g\|)^M$, because $\|g\| \leq T$. Integrate and use (1) with $50r^2 + 1 \leq 99r^2$. $\square$

Item 3 is not used in this section. The last section uses it for the coefficient bound of the local bounds.

### Decay of the average

**Lemma.** Let $b \geq 2$ and $\ell(x) \leq b^{5n}$. For $s \in R$ and $y \in G_1$, $\ell(y)/b^{6n} \leq \|x^{-1}sy\|/2$.

Lean: `New.besselLength_div_le_half_norm` (New/Spanning/Bessel/CutTailBound.lean).

*Proof.* By the lemma on the length, $\ell(y) = \ell(sy) \leq \|x^{-1}sy\|\,\ell(x) \leq \|x^{-1}sy\|\,b^{5n}$. Divide by $b^{6n}$ and use $b^n \geq 2$. $\square$

**Lemma (Decay of the average).** Let $\|v\| = 1$, $b \geq 2$, $\ell(x) \leq b^{5n}$ and $i \leq A$. Then for all $y$,
$$\ell_b(y)^i\,\|W_x(y)\| \leq \int_R\Bigl(\frac{2}{\|x^{-1}sy\|}\Bigr)^M ds.$$

Lean: `New.scaledBesselLength_pow_mul_enorm_besselAverage_le` (New/Spanning/Bessel/CutTailBound.lean).

*Proof.* Bound $\|W_x(y)\|$ by $\int_R|c_\lambda(x^{-1}sy)|\,ds$ and move $\ell_b(y)^i$ inside. Put $g = x^{-1}sy$. If $\ell_b(y) = 1$, the decay lemma with $j = 0$ gives $|c_\lambda(g)| \leq (2/\|g\|)^M$. Otherwise $\ell_b(y) \leq \|g\|/2$ by the previous lemma, and the decay lemma with $j = i$ gives $\ell_b(y)^i|c_\lambda(g)| \leq (\|g\|/2)^i(2/\|g\|)^{i}(2/\|g\|)^M$. $\square$

So the free part $A$ of the gap becomes decay in $\ell$. The source uses $i = 3r^3f$, which needs $3r^3f \leq A$. For the data $D$, $A = r^7$ and $f$ is the number of infinite places.

### The cutoff

**Definition.** For $R > 0$ and $t \in \mathbb{R}$, $\chi_R(t) = \max(0, \min(1, 2 - 2t/R))$. For a continuous $F$, the cut is $F^\flat(y) = \chi_{b^{6n+2}}(\ell(y))\,F(y)$.

Lean: `New.besselCutoff`, `New.besselCut` (New/Spanning/Bessel/CutTailBound.lean).

So $\chi_R(t) = 1$ for $t \leq R/2$, $\chi_R(t) = 0$ for $t \geq R$, and $\chi_R$ is linear in between. The cut is continuous because $\ell$ is continuous.

**Lemma.** Let $b > 0$ and let $F$ be continuous.

1. $\|F^\flat(y)\| \leq \|F(y)\|$ and $\|F^\flat(y) - F(y)\| \leq \|F(y)\|$.
2. $F^\flat(y) \neq 0$ implies $\ell(y) \leq b^{6n+2}$.
3. $F^\flat(y) \neq F(y)$ implies $\ell(y) > b^{6n+2}/2$.
4. If $F$ is a Bessel function for $\rho$, then so is $F^\flat$.

Lean: `New.enorm_besselCut_le`, `New.enorm_besselCut_sub_le`, `New.inCut_of_besselCut_ne_zero`, `New.lt_besselLength_of_besselCut_ne`, `New.IsBesselFunction.besselCut` (New/Spanning/Bessel/CutTailBound.lean).

*Proof.* (1) $\chi$ takes values in $[0, 1]$. (2) and (3) are the two values of $\chi$ outside the middle range. (4) A continuous bounded real function that is left invariant under $S$ multiplies a Bessel function into a Bessel function (`New.IsBesselFunction.smul_of_invariant`), and $\ell$ is left invariant under $S$. $\square$

**Lemma (The cut is close).** Let $b \geq 2$, $r \geq 100$ and $f \neq 0$. If $(A, a)$ is a decay majorant for the family $\operatorname{select}(F, F^\flat)$, then
$$\int_{\mathsf U\backslash G_1}\|F^\flat - F\|^2 \leq b^{-2r^3f}\,|I|.$$

Lean: `New.IsDecayMajorant.lintegral_sq_besselCut_sub_le` (New/Spanning/Bessel/CutTailBound.lean).

*Proof.* Where $F^\flat(y) \neq F(y)$, item 3 of the lemma and the lemma on the scaled length give $\ell_b(y) \geq b$. So $b^{3r^3f}\|F^\flat(y) - F(y)\| \leq \ell_b(y)^{3r^3f}\|F(y)\| \leq A(y) \leq a$. Elsewhere the difference is $0$. Multiply the two bounds $b^{3r^3f}\|F^\flat - F\| \leq A$ and $b^{3r^3f}\|F^\flat - F\| \leq a$ and integrate: $b^{6r^3f}\int\|F^\flat - F\|^2 \leq a\int A \leq b^{400r^2}|I|$. Since $r \geq 100$, $400r^2 \leq 4r^3 \leq 4r^3 f$, so $b^{400r^2 - 6r^3f} \leq b^{-2r^3f}$. $\square$

### The majorant of the normalized average

**Lemma.** For $t \in S$ and measurable $\varphi \geq 0$, $\int_R\varphi(x^{-1}sty)\,ds = \int_R\varphi(x^{-1}sy)\,ds$.

Lean: `New.lintegral_besselGraph_mul_eq` (New/Spanning/Bessel/CutTailBound.lean).

*Proof.* Lift $t$ to an element of $R$ and use the right invariance of $ds$. $\square$

**Lemma.** A finite nonzero $q \in [0, \infty]$ and a natural number $k$ admit a real $c$ with $|c|^2q = k$.

Lean: `New.exists_enorm_sq_mul_eq` (New/Spanning/Bessel/CutTailBound.lean).

**Theorem (Majorant).** Let $\|v\| = 1$, $\ell(x) \leq b^{5n}$, $b \geq 2000$, $r + L + 1 \leq b^4$, $m + 99r^2 \leq 400r^2$ and $3r^3f \leq A$. Assume
$$\operatorname{vol}_x \leq b^m\,d_\lambda\int_{\mathsf U\backslash G_1}\|W_x\|^2,$$
and let $F = cW_x$ with $\int\|F\|^2 = |I|$. Then the family $\operatorname{select}(F, F^\flat)$ has a decay majorant.

Lean: `New.exists_isDecayMajorant_besselAverage` (New/Spanning/Bessel/CutTailBound.lean).

*Proof.* Put $\varphi(g) = (2/\|g\|)^M$ and $\Phi(y) = \int_R\varphi(x^{-1}sy)\,ds$. The majorant is $A = |c|\Phi$ with the bound $a = |c|\,16^M\operatorname{vol}_x$.

1. $A$ is measurable, and left invariant under $S$ by the previous lemma.
2. For $F$, item 2 is the decay of the average with $i = 3r^3f$. For $F^\flat$ use $\|F^\flat\| \leq \|F\|$.
3. $A \leq a$ is the covering bound of [the section on averages](/chapter/bessel-real-place/#bessel-functions-as-averages).
4. Unfolding gives $\int_{\mathsf U\backslash G_1}\Phi = \int_{G_1}\varphi$. So
$$a\int A = |c|^2\,16^M\operatorname{vol}_x\int_{G_1}\varphi \leq |c|^2\|W_x\|_2^2\cdot b^m\cdot d_\lambda\int_{G_1}\varphi\cdot 16^M \leq |I|\,b^m\,b^{99r^2},$$
by the hypothesis, by $|c|^2\|W_x\|_2^2 = |I|$, and by item 2 of the tail lemma. Then $m + 99r^2 \leq 400r^2$. $\square$

The volume $\operatorname{vol}_x$ appears in the bound $a$ and cancels against $\|W_x\|_2^2$ through the hypothesis. This is the reason for the large period of [the previous section](/chapter/bessel-real-place/#a-point-with-a-large-period).

### The cut pair

**Theorem (Cut pair).** Let $\rho$ be continuous and the hypotheses of the previous theorem hold, with $r \geq 100$ and $f \neq 0$. Then there are $c \in \mathbb{R}$ and a continuous $F$ with $F = cW_x$, $F * e_\lambda = F$, and $\operatorname{select}(F, F^\flat)$ a cut pair for $b$, $f$ and $\rho$.

Lean: `New.exists_isCutPair_besselAverage` (New/Spanning/Bessel/CutTailBound.lean).

*Proof.* $W_x$ is a Bessel function and integrable, so $q = \int\|W_x\|^2$ is finite. The hypothesis and $\operatorname{vol}_x > 0$ give $q \neq 0$. Choose $c$ with $|c|^2q = |I|$. Then $F = cW_x$ is a Bessel function, continuous, integrable, reproduced by $e_\lambda$, and $\int\|F\|^2 = |I|$. The fields of the cut pair follow from the lemmas of this section: item 3 from $\|F^\flat\| \leq \|F\|$, items 4 and 6 from the cutoff, item 5 from the lemma on the closeness of the cut with the majorant of the previous theorem. $\square$

**Remark (Formalization).** The constant $c$ is given by an existence statement, and the source does not fix its sign. Any $c$ with $|c|^2 q = |I|$ gives a cut pair. The docstring of the majorant theorem states the hypothesis as $m \leq 301r^2$, while the Lean hypothesis is $m + 99r^2 \leq 400r^2$. The two are the same condition.

**Example.** Take $b = 2000$, $r = 100$ and $f = 1$. Then the cut region is $\ell \leq 2000^{6n+2}$, the majorant decays like $\ell_b^{-3 \cdot 10^6}$, and item 5 gives $\|W^\flat - W\|_2^2 \leq 2000^{-2 \cdot 10^6}|I|$. The bound $b^{400r^2} = 2000^{4 \cdot 10^6}$ of the majorant is larger than $|I|$ by a big factor, but the decay exponent $3r^3f$ is larger again, and only the difference matters in the closeness lemma. In the data $D$ the numbers are much larger, but the comparison $400r^2 \leq 6r^3f - 2r^3f$ is the same. At $r = 100$ and $f = 1$ it is an equality.
