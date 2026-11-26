---
title: The dimension formula and the theta group
lean:
  - Lib/Shimura/ComplexTheta/DimensionFormula.lean
decls:
  - New.IsAppellHumbert.poincareSeries_mem_thetaSpace_and_quotMean
  - New.IsAppellHumbert.exists_mem_thetaSpace_ne_zero
  - New.IsAppellHumbert.finrank_sq_eq_relIndex
  - New.IsAppellHumbert.thetaSpace_le_of_thetaShift_mem
  - New.IsAppellHumbert.schur_lemma
  - New.IsAppellHumbert.exists_mem_thetaSpace_nsmul_apply_ne_zero
  - New.ThetaTori.canonicalMultiplier
  - New.ThetaTori.isAppellHumbert_canonicalMultiplier
  - New.ThetaTori.normalizedShift
  - New.IsAppellHumbert.normalizedShift_normalizedShift
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The dimension formula and the theta group

This section proves the three facts about theta functions that the rest of the chapter needs. For Appell-Humbert data $(B, \chi)$ with positive Riemann form on a full-rank lattice $L$:

1. the space $\Theta(B, \chi)$ of theta functions of type $(B, \chi)$ is finite-dimensional and not zero, and $(\dim \Theta(B, \chi))^2 = [L^\perp : L]$;
2. the twisted translations $T_a$, $a \in L^\perp$, act irreducibly on $\Theta(B, \chi)$;
3. for $n \geq 2$ the theta functions of type $(nB, \chi^n)$ have no common zero.

The first is the dimension formula of Frobenius. The textbooks state it with elementary divisors $d_1 \mid \cdots \mid d_g$ of $E$ on $L$: $\dim \Theta = d_1 \cdots d_g$ (Birkenhake and Lange, *Complex Abelian Varieties*, Chapter 3; Mumford, *Abelian Varieties*, Section 3). As $L^\perp/L \cong \bigoplus_i (\mathbb{Z}/d_i)^2$, the two forms agree.

Throughout the section, $V$ is a finite-dimensional complex space, $L$ is a full-rank lattice in $V$, and $(B, \chi)$ is Appell-Humbert data for $L$ with Riemann form $E$. We write $\Theta(B, \chi)$ for the space of theta functions.

### The model case

For the lattice $L = \mathbb{Z} + \tau\mathbb{Z}$ and the form $nB$ of [Section 2](/chapter/complex-abelian-varieties/), the space $\Theta(nB, \chi^n)$ has the basis
$$\vartheta_k(z) = \sum_{m \in \mathbb{Z}} \exp\Bigl(\pi i n \bigl(m + \tfrac{k}{n}\bigr)^2\tau + 2\pi i n\bigl(m + \tfrac{k}{n}\bigr) z\Bigr) \qquad (k \in \mathbb{Z}/n),$$
and $\vartheta_0$ is $\vartheta$ for $n = 1$. Each $\vartheta_k$ has the factors $1$ at $l = 1$ and $\exp(-\pi i n\tau - 2\pi i n z)$ at $l = \tau$, so it has type $(nB, \chi^n)$. So $\dim = n$, and $[L^\perp : L] = [\tfrac{1}{n}L : L] = n^2$. The twisted translations by $\tfrac{1}{n}$ and $\tfrac{\tau}{n}$ act on this basis, up to scalars, as a cyclic shift and as a diagonal matrix of $n$-th roots of unity. These generate $M_n(\mathbb{C})$. This is statement 2 in the model case.

### Existence

The first step is a nonzero theta function. The classical construction averages a Gaussian over $L$.

**Proposition.** Assume that $\operatorname{Re} B(x, x) > 0$ for all $x \neq 0$. Put
$$K(x, y) = \sum_{l \in L} \frac{1}{\chi(l)}\exp\Bigl(B(x, y - x + l) - B(l, y) - \frac{B(l, l)}{2}\Bigr).$$
Then: (a) the series converges for all $x, y \in V$; (b) $K$ is jointly continuous; (c) for each $x$, the function $y \mapsto K(x, y)$ is a theta function of type $(B, \chi)$; (d) the mean of $x \mapsto K(x, x)$ over $V/L$ is $\chi(0)^{-1}$; (e) $K(w, w) \neq 0$ for some $w \in V$.

Lean: `New.IsAppellHumbert.poincareSeries_mem_thetaSpace_and_quotMean` (Lib/Shimura/ComplexTheta/DimensionFormula.lean).

*Proof.* The real part of the exponent is $-\operatorname{Re} B(l, l)/2$ plus terms linear in $l$, and $\operatorname{Re} B(l, l) \geq c|l|^2$ for some $c > 0$, so the series converges normally (`New.IsAppellHumbert.summable_and_analyticAt_tsum`). For (c), the change $l \mapsto l + m$ of the summation index gives the factor $\chi(m)\exp(B(m, y) + B(m, m)/2)$, by the semicharacter condition. For (d), on the diagonal the series is a Fourier series $\sum_l \mathbf{e}(E(x, l))\, c_l$ on $V/L$, because $L \subseteq L^\perp$. Its mean is the coefficient at $l = 0$, which is $\chi(0)^{-1} \neq 0$, and (e) follows. $\square$

**Remark.** The condition 3 of the Appell-Humbert data at $l = m = 0$ gives $\chi(0) = \chi(0)^2$, so $\chi(0) = 1$. The mean in (d) is $1$.

The hypothesis $\operatorname{Re} B(x, x) > 0$ is not the positivity of $E$. It depends on the symmetric part $S$ of $B$ (Section 2). The next proof removes $S$.

**Theorem.** If the Riemann form of $B$ is positive, there is a nonzero theta function of type $(B, \chi)$.

Lean: `New.IsAppellHumbert.exists_mem_thetaSpace_ne_zero` (Lib/Shimura/ComplexTheta/DimensionFormula.lean).

*Proof.* Let $T(u, v) = \frac{i}{2}\bigl(B(iu, v) + iB(u, v)\bigr)$. This is minus the part of $B$ that is complex-linear in $u$, and it is symmetric (`New.IsAppellHumbert.linearPart_symm`). So $B + T$ has the same Riemann form as $B$, and $(B + T, \chi)$ is Appell-Humbert data. The form $B + T$ is of hermitian type, $B + T = \pi\overline{H}$, so $\operatorname{Re}(B + T)(x, x) = \pi H(x, x) = \pi E(x, ix) > 0$ for $x \neq 0$. The proposition gives $w$ with $K(w, w) \neq 0$ for $(B + T, \chi)$. Then $f(y) = \exp(T(y, y)/2)\,K(w, y)$ is a theta function of type $(B, \chi)$, and $f(w) \neq 0$. $\square$

### The dimension formula

**Theorem (Frobenius).** Assume that the Riemann form of $B$ is positive. Then:

1. the twisted translations $T_a|_{\Theta(B, \chi)}$, $a \in L^\perp$, span the algebra $\operatorname{End}_{\mathbb{C}} \Theta(B, \chi)$;
2. $\bigl(\dim_{\mathbb{C}} \Theta(B, \chi)\bigr)^2 = [L^\perp : L]$;
3. $\dim_{\mathbb{C}} \Theta(B, \chi) > 0$.

Lean: `New.IsAppellHumbert.finrank_sq_eq_relIndex` (Lib/Shimura/ComplexTheta/DimensionFormula.lean).

**Remark.** In Lean the dimension is `Module.finrank`, which is $0$ for an infinite-dimensional space, and the index is `AddSubgroup.relIndex`, which is $0$ for an infinite index. So part 2 alone would hold with $0 = 0$ if both were infinite. The source excludes this. It proves that $\Theta(B, \chi)$ is finite-dimensional (`New.IsAppellHumbert.finite_thetaSpace`), that $L^\perp/L$ is finite (`New.IsAppellHumbert.finite_dualLattice_quotient`), and part 3. So part 2 is a true equality of positive integers.

*Proof.* Put $n = \dim \Theta(B, \chi)$ and $N = [L^\perp : L]$. The proof has four steps.

*Step 1: $L^\perp/L$ is finite.* A positive Riemann form is nondegenerate (`New.IsPosRiemann.nondegenerate`). So $L^\perp$ is the dual lattice of $L$ for a nondegenerate form, a full-rank lattice of the same rank, and it contains $L$ by `New.IsAppellHumbert.le_dualLattice`.

*Step 2: an inner product and $n^2 \leq N$.* For theta functions $s, t$ of type $(B, \chi)$ the function $x \mapsto \overline{(T_x s)(0)}\,(T_x t)(0)$ is periodic under $L$. Its mean over $V/L$ is a positive inner product on $\Theta(B, \chi)$. The source puts a holomorphic parameter $b$ into the integrand and gets a mean $m(s, t; b)$ that is entire in $b$. A Liouville argument shows that $m(s, t; 0) = 0$ forces $m(t, s; b) = 0$ for all $b$ (`pairingMean_eq_zero_of_eq_zero`, a private lemma). The characters $x \mapsto \mathbf{e}(E(x, a))$, $a \in L^\perp$, separate the points of $V/L$ (`New.IsPosRiemann.isDualFamily`). With this, the source builds from $n$ independent theta functions an injective linear map from $\Theta(B, \chi)^n$ to the functions on $L^\perp/L$ (`New.IsAppellHumbert.exists_injective_to_dual_quotient`). So $n \cdot n \leq N$, and $\Theta(B, \chi)$ is finite-dimensional.

*Step 3: $N \leq n^2$.* Choose representatives $a_q \in L^\perp$ of the classes $q \in L^\perp/L$. The $N$ operators $T_{a_q}$ are linearly independent in $\operatorname{End}\Theta(B, \chi)$ (`New.IsAppellHumbert.linearIndependent_thetaShiftEnd_out`). Indeed, by the commutation rule of [Section 2](/chapter/complex-abelian-varieties/), conjugation by $T_y$, $y \in L^\perp$, multiplies $T_{a_q}$ by $\mathbf{e}(E(y, a_q))$. Distinct classes give distinct characters of $L^\perp$, since $E$ is nondegenerate, and eigenvectors for distinct characters are independent. Hence $N \leq n^2$.

*Step 4: conclusion.* Steps 2 and 3 give $N = n^2$ (`New.IsAppellHumbert.relIndex_dualLattice_eq_finrank_end`). The $N$ independent operators $T_{a_q}$ lie in a space of dimension $n^2 = N$, so they span it. This is part 1. Part 3 is the theorem on existence. $\square$

**Corollary (Irreducibility).** Assume that the Riemann form of $B$ is positive. Let $f \neq 0$ be a theta function of type $(B, \chi)$, and let $S$ be a complex subspace of the functions $V \to \mathbb{C}$ that contains $T_a f$ for all $a \in L^\perp$. Then $\Theta(B, \chi) \subseteq S$.

Lean: `New.IsAppellHumbert.thetaSpace_le_of_thetaShift_mem` (Lib/Shimura/ComplexTheta/DimensionFormula.lean).

*Proof.* Let $g \in \Theta(B, \chi)$. Choose a linear form $\ell$ with $\ell(f) = 1$. The endomorphism $h \mapsto \ell(h)\,g$ lies in the span of the $T_a$ by part 1 of the theorem. The endomorphisms that map $f$ into $S$ form a subspace that contains all $T_a$. So it contains $h \mapsto \ell(h) g$, which maps $f$ to $g$. $\square$

**Corollary (Schur's lemma).** Assume that the Riemann form of $B$ is positive. An endomorphism $Q$ of $\Theta(B, \chi)$ that commutes with all $T_a$, $a \in L^\perp$, is a scalar.

Lean: `New.IsAppellHumbert.schur_lemma` (Lib/Shimura/ComplexTheta/DimensionFormula.lean).

*Proof.* $Q$ commutes with the span of the $T_a$, which is the whole matrix algebra by part 1. The center of a matrix algebra over $\mathbb{C}$ is $\mathbb{C}$. $\square$

A last consequence: the integer $N = [L^\perp : L]$ is positive and kills $L^\perp/L$, so $N a \in L$ for every $a \in L^\perp$ (`New.IsAppellHumbert.exists_nsmul_mem_of_mem_dualLattice`).

### No base points

**Theorem.** Assume that the Riemann form of $B$ is positive. Let $z \in V$ and let $n > 1$ be an integer. Then some theta function $f$ of type $(nB, \chi^n)$ has $f(z) \neq 0$.

Lean: `New.IsAppellHumbert.exists_mem_thetaSpace_nsmul_apply_ne_zero` (Lib/Shimura/ComplexTheta/DimensionFormula.lean).

*Proof.* Write $n = m + 1$ with $m \geq 1$, and take a nonzero theta function $f$ of type $(B, \chi)$. Products of theta functions are theta functions of the sum type (`New.thetaSpace.mul`, `New.thetaSpace.pow`). For $a \in V$ consider
$$F_a = T^{mB}_a(f^m) \cdot T^{B}_{-ma} f,$$
where the superscript names the form of the twisted translation. By the proposition on $T_a f$ in [Section 2](/chapter/complex-abelian-varieties/), the characters of the two factors cancel, so $F_a$ has type $(nB, \chi^n)$. If all theta functions of this type vanish at $z$, then $F_a(z) = 0$ for all $a$. Up to a nonzero exponential, $F_a(z) = f(z + a)^m f(z - ma)$. By the identity theorem (`New.ThetaTori.eq_zero_of_differentiable_of_mul_eq_zero`) one factor is zero as a function of $a$, so $f = 0$, a contradiction. $\square$

This is the analytic half of the theorem of Lefschetz (Mumford, *Abelian Varieties*, Section 3). The other half, that $L^n$ embeds the torus for $n \geq 3$, is not proved. The source does not need it, because it starts from a given projective embedding.

### The canonical multiplier and the Heisenberg law

To compare theta functions on different tori, the source fixes a multiplier that is determined by the form. Let $b \colon V \to V$ be a complex-linear map.

**Definition (Canonical multiplier).** The *canonical multiplier* of $b$ is $\chi_b(x) = \exp\bigl(\pi i E(bx, x)\bigr)$ for $x \in V$.

Lean: `New.ThetaTori.canonicalMultiplier` (Lib/Shimura/ComplexTheta/DimensionFormula.lean).

**Proposition.** Let $B$ be a real-complex form with Riemann form $E$. Assume:

1. $E(bu, w) = E(u, w) - E(u, bw)$ for all $u, w \in V$;
2. $\operatorname{Re} B(u, w) = \operatorname{Re} B(w, u)$ for all $u, w \in V$;
3. $E(bl, m) \in \mathbb{Z}$ for all $l, m \in L$.

Then $(B, \chi_b)$ is Appell-Humbert data for $L$.

Lean: `New.ThetaTori.isAppellHumbert_canonicalMultiplier` (Lib/Shimura/ComplexTheta/DimensionFormula.lean).

*Proof.* $|\chi_b| = 1$, since $E$ is real. For $l, m \in L$, hypothesis 1 and the antisymmetry of $E$ give
$$E(b(l + m), l + m) = E(bl, l) + E(bm, m) + E(m, l) + 2E(bl, m).$$
By hypothesis 3, $E(bl, m)$ is an integer, so the term $2E(bl, m)$ contributes $\exp(2\pi i E(bl, m)) = 1$. What remains is the semicharacter condition. $\square$

Hypothesis 1 says that $b + b^* = 1$ for the adjoint $b^*$ of $b$ for $E$. For $b = \frac{1}{2}$, $\chi_b = 1$ and hypothesis 3 asks that $E$ be even on $L$. In the PEL setting of [the next chapter](/chapter/integral-model/), $b$ is an integer $\beta$ of the CM field with $\bar\beta = 1 - \beta$ (the field `star_beta` of the PEL datum).

**Definition (Normalized translation).** The *normalized translation* by $x \in V$ is $U_x = \chi_b(x)^{-1}\,T_x$.

Lean: `New.ThetaTori.normalizedShift` (Lib/Shimura/ComplexTheta/DimensionFormula.lean).

A function $f$ is a theta function of type $(B, \chi_b)$ if and only if it is entire and $U_l f = f$ for all $l \in L$ (`New.ThetaTori.mem_thetaSpace_iff_normalizedShift`). So the normalized translations by $L$ act trivially, and those by $L^\perp$ act on $\Theta(B, \chi_b)$ through $L^\perp/L$.

**Proposition (Heisenberg law).** Let $(B, \chi)$ be Appell-Humbert data for $L$, for some multiplier $\chi$, and let $b$ satisfy hypothesis 1 above. Then for all $x, y \in V$ and every function $f \colon V \to \mathbb{C}$,
$$U_x U_y f = \mathbf{e}\bigl(E(bx, y)\bigr)\,U_{x + y} f.$$

Lean: `New.IsAppellHumbert.normalizedShift_normalizedShift` (Lib/Shimura/ComplexTheta/DimensionFormula.lean).

*Proof.* By the composition law of [Section 2](/chapter/complex-abelian-varieties/), $T_x T_y = \exp(\pi i E(x, y))T_{x + y}$. The multipliers at $x$, $y$ and $x + y$ contribute $\exp(\pi i(E(bx, y) + E(by, x)))$, and hypothesis 1 gives $E(by, x) = E(bx, y) - E(x, y)$. The factors $\exp(\pm\pi i E(x, y))$ cancel. $\square$

The multiplier $\chi$ enters only through the symmetry of $\operatorname{Re} B$. The cocycle $(x, y) \mapsto \mathbf{e}(E(bx, y))$ is bilinear. This is the form of the theta structures of [Section 5](/chapter/complex-abelian-varieties/): there the lift of the translation by $s$ sends $X_t$ to $c_s(t) X_{s + t}$ with a character $c_s$.
