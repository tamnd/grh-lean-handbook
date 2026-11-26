---
title: Small roots
lean:
  - New/OneLift/FalseLifts/HyperbolicPlaneStep.lean
decls:
  - New.SiegelWeil.eq_zero_of_heckePolyOp_eq_zero
  - New.SiegelWeil.norm_frobValue
  - New.SiegelWeil.qPochhammer_ne_zero
  - New.SiegelWeil.lift_eq_zero_of_heckePolyOp_eq_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Small roots

The Hecke polynomial $H_w(X)$ has the constant term $1$. If $|X|$ is small, the other terms are small, and a bounded function that $H_w(X)$ kills must be zero. This section makes the bound exact. It then combines it with the Hecke transfer, so that a Hecke equation on $U(V)$ kills the bounded descents to a smaller group. The hyperbolic plane step of [Section 6](/chapter/false-lifts/#the-hyperbolic-plane-step) uses the result once for each plane.

### Background

Let $w$ be a finite place, split over $E^+$, with residue field $k_w$ of order $q$. At $w$ the unitary group of rank $m$ is $GL_m(E_w)$. For a subspace $U$ of $k_w^m$, let $\gamma_U$ be the coset representative `basicCosetRep U` at $w$ and $1$ elsewhere. For a function $F$ that is spherical at $w$, the Hecke polynomial acts by

$$H_w(X) F(g) = \sum_{U \leq k_w^m} c(X, U)\, F(g\gamma_U), \qquad c(X, U) = (-X)^{\dim U} q^{\binom{\dim U}{2}}.$$

This is `heckePolyOp_eq_sum`, with $c(X, U) = $ `New.heckePolyCoeff X U`. We use three facts from Volume 6, stated in [a maximum principle at a split place](/chapter/siegel-weil/#a-maximum-principle-at-a-split-place).

- The $q$-binomial theorem (`New.q_binomial_submodule`): $\sum_{U \leq k_w^m} c(X, U) = (X; q)_m = \prod_{j < m}(1 - q^jX)$.
- The maximum principle (`New.SiegelWeil.maximum_principle`): if $v$ is bounded above, $\sum_i |a_i| < \lambda$ and $\lambda v(x) \leq \sum_i |a_i| v(r(x, i))$ for all $x$, then $v \leq 0$.
- The Hecke transfer (`New.SiegelWeil.lift_swap_heckePolyOp`): let $W'$ have rank $m$ and $V$ rank $m + k$, let $\chi$ be unramified at $\bar w$, let the datum $\phi$ be the vacuum at $\bar w$, and let $Y$ be rapid and spherical at $w$. Then the descent $F$ of $Y$ to $W'$ by $\phi$ with the character $\chi$ is spherical at $w$, and the descent of $H_w(X)Y$ is $(X_0; q)_k\, H_w(X')F$, with

$$X_0 = \chi.\mathrm{frobValue}(m, \bar w)\, X, \qquad X' = \frac{q^k\, \chi.\mathrm{frobValue}(m, \bar w)}{1.\mathrm{frobValue}(n, \bar w)}\, X.$$

### A bounded function killed by a Hecke polynomial

**Theorem (Small roots).** Let $w$ be split of norm $q$, and let $F$ be a bounded function on the adelic unitary group of rank $m$, spherical at $w$. If $H_w(X)F = 0$ and $q^{m+1}|X| \leq 1$, then $F = 0$.

Lean: `New.SiegelWeil.eq_zero_of_heckePolyOp_eq_zero` (New/OneLift/FalseLifts/HyperbolicPlaneStep.lean).

*Proof.* For every $g$ we have $\sum_U c(X, U) F(g\gamma_U) = 0$.

*Step 1: the total weight is below $2$.* By the $q$-binomial theorem at the point $-|X|$, and since $|c(X, U)| = c(-|X|, U)$,

$$\sum_U |c(X, U)| = \prod_{j < m}(1 + q^j|X|) \leq \exp\Big(\sum_{j<m} q^j|X|\Big).$$

The geometric sum satisfies $\sum_{j < m} q^j < q^m$. Since $q \geq 2$, the hypothesis gives $q^m|X| \leq q^{-1} \leq \frac12$. So the total weight is at most $\exp(\frac12) < 2$, as $\log 2 > \frac12$.

*Step 2: isolate the term $U = 0$.* The coefficient of $U = 0$ is $c(X, 0) = 1$. Apply the relation at $g\gamma_0^{-1}$:

$$F(g) = -\sum_{U \neq 0} c(X, U)\, F(g\gamma_0^{-1}\gamma_U).$$

So $|F(g)| \leq \sum_{U \neq 0}|c(X, U)|\,|F(g\gamma_0^{-1}\gamma_U)|$. Add $|F(g)| = |c(X,0)|\,|F(g\gamma_0^{-1}\gamma_0)|$ to both sides:

$$2|F(g)| \leq \sum_U |c(X, U)|\, |F(g\gamma_0^{-1}\gamma_U)|.$$

*Step 3.* Apply the maximum principle with $v = |F|$, $\lambda = 2$, $a_U = c(X, U)$ and $r(g, U) = g\gamma_0^{-1}\gamma_U$. By step 1, $\sum_U|a_U| < 2$. So $|F| \leq 0$, and $F = 0$. $\square$

**Example.** Let $m = 1$. The subspaces of $k_w$ are $0$ and $k_w$, with $c(X, 0) = 1$ and $c(X, k_w) = -X$. The relation at $g\gamma_0^{-1}$ is $F(g) = XF(g\gamma)$ with $\gamma = \gamma_0^{-1}\gamma_{k_w}$. So $\sup|F| \leq |X| \sup|F|$, and $|X| \leq q^{-2} < 1$ gives $F = 0$. The condition $q^{m+1}|X| \leq 1$ is stronger than needed when $m = 1$. It is the form that is convenient for every $m$.

**Remark (Formalization).** Boundedness is `BddAbove` of the range of $|F|$. No measurability or continuity is needed. The proof does not use the group structure beyond the right translations $g \mapsto g\gamma_0^{-1}\gamma_U$.

### Two small facts

**Lemma (The modulus of a Frobenius value).** For a character $\chi$ of $U(1)$, a finite type $m$ and a finite place $w$, $|\chi.\mathrm{frobValue}(m, w)| = \sqrt{q}^{\,\#m}$.

Lean: `New.SiegelWeil.norm_frobValue` (New/OneLift/FalseLifts/HyperbolicPlaneStep.lean).

*Proof.* By definition, `frobValue` is $\sqrt q^{\,\#m}$ times the value of a unitary Hecke character at a uniformiser, and this value has modulus $1$. $\square$

**Lemma (A nonzero product).** If $q > 1$ and $q^k|X| \leq 1$, then $(X; q)_k \neq 0$.

Lean: `New.SiegelWeil.qPochhammer_ne_zero` (New/OneLift/FalseLifts/HyperbolicPlaneStep.lean).

*Proof.* If the factor $1 - q^iX$ is $0$ for some $i < k$, then $q^i|X| = 1$, so $X \neq 0$. Then $q^k|X| > q^i|X| = 1$, a contradiction. $\square$

### Bounded descents of a Hecke eigenfunction

**Theorem (Bounded descents vanish).** Let $Y$ be automorphic on $U(V)$, with $V$ definite of rank $n$, spherical at the split place $w$ and killed by $H_w(X)$. Let $\chi$ be a character of $U(1)$ whose base change is unramified at $\bar w$, and let $\phi$ be a datum on $\mathrm{Hom}(W', V)$ that is the vacuum at $\bar w$. Let $W'$ have rank $m$, and $n = m + k$. Assume

$$\sqrt q^{\,m + 2k}|X| \leq 1 \qquad\text{and}\qquad \sqrt q^{\,2(m+1) + k}|X| \leq 1.$$

If the descent $F$ of $Y$ to $W'$ by $\phi$, with the kernel twisted by $\chi$, is bounded, then $F = 0$.

Lean: `New.SiegelWeil.lift_eq_zero_of_heckePolyOp_eq_zero` (New/OneLift/FalseLifts/HyperbolicPlaneStep.lean).

*Proof.* The function $Y$ is rapid on the compact quotient. The trivial character is unramified at $\bar w$. So the Hecke transfer applies: $F$ is spherical at $w$, and

$$0 = \text{descent of } H_w(X)Y = (X_0; q)_k\, H_w(X')F.$$

By the modulus of Frobenius values, $|X_0| = \sqrt q^{\,m}|X|$ and

$$|X'| = \frac{q^k \sqrt q^{\,m}}{\sqrt q^{\,m+k}}|X| = \sqrt q^{\,k}|X|.$$

The first assumption says $q^k|X_0| = \sqrt q^{\,2k+m}|X| \leq 1$. So $(X_0; q)_k \neq 0$ by the lemma on a nonzero product, and $H_w(X')F = 0$. The second assumption says $q^{m+1}|X'| = \sqrt q^{\,2(m+1)+k}|X| \leq 1$. By the theorem on small roots, $F = 0$. $\square$

### The exponents in the tower

In the tower, $V = I_n$ and $X = x_w$ up to conjugation, so $|X| = (\sqrt q^{\,r} q^{n-r-1})^{-1} = \sqrt q^{\,-d}$ with $d = r + 2(n - r - 1)$. Let $W'$ be $W$ plus $l + 1$ planes, so $m = r + 2(l+1)$ and $k = n - m$. The two exponents of the last theorem are

$$m + 2k = 2n - m = 2n - r - 2l - 2, \qquad 2(m+1) + k = n + m + 2 = n + r + 2l + 4.$$

Both are at most $d = 2n - r - 2$ when $2r + 2l + 6 \leq n$, which follows from the rank condition $2r + 2(l+1) + 3 < n$ of the tower. Since $\sqrt q \geq 1$, the conditions $\sqrt q^{\,j}|X| \leq 1$ hold for these $j$. This is the computation `h_size` in the proof of `descentsVanish_add_planes`. It is the source of the rank condition of [Section 1](/chapter/false-lifts/#what-the-chapter-proves).
