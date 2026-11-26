---
title: A maximum principle at a split place
lean:
  - Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean
  - Lib/Weil/Unramified/HeckeTransfer.lean
  - Lib/General/Combinatorics.lean
decls:
  - New.SiegelWeil.maximum_principle
  - New.SiegelWeil.prod_mul_prod_lt_prod_one_add_pow
  - New.SiegelWeil.transferWeight
  - New.SiegelWeil.transferPoint
  - New.SiegelWeil.norm_qPochhammer_mul_norm_eq_norm_sum
  - New.SiegelWeil.norm_qPochhammer_neg
  - New.SiegelWeil.norm_transferWeight
  - New.SiegelWeil.sum_norm_transferWeight_lt
  - New.SiegelWeil.exists_zeroTerm_transferPoint_eq
  - New.SiegelWeil.sum_norm_mul_norm_zeroTerm_le
  - New.SiegelWeil.eq_zero_of_le_tsum_zeroTerm
status: drafted
drafted_by: writer@claude-opus-5-5
---
## A maximum principle at a split place

This section proves the criterion that kills the difference $\ell$ of the two sides of the formula: a functional invariant under $G_T$ is zero if, up to an additive constant, it is bounded on the translates of each vector by the Eisenstein series of the vacuum. The Hecke operator at a split place is a weighted mean of translates. By the Hecke transfer of [Volume 5](/chapter/iwahori-satake/) it acts on matrix coefficients of the Weil representation by a scalar that exceeds the total weight exactly when $2p < m$, and the Eisenstein series of the vacuum satisfies the opposite inequality term by term. A maximum principle then gives $\ell = 0$.

**Theorem (Maximum principle).** Let $X$ be a set, $\iota$ a finite set, $v : X \to \mathbb{R}$ bounded above, $a : \iota \to \mathbb{C}$, $r : X \times \iota \to X$ and $\lambda \in \mathbb{R}$. Suppose that $\sum_{i} \|a_i\| < \lambda$ and that for all $x \in X$,
$$\lambda\, v(x) \le \sum_{i} \|a_i\|\, v(r(x, i)).$$
Then $v(x) \le 0$ for every $x \in X$.

Lean: `New.SiegelWeil.maximum_principle` (Lib/Weil/Unramified/HeckeTransfer.lean).

*Proof.* Let $M = \sup v$. For every $y$, $\lambda v(y) \le (\sum_i \|a_i\|) M$, so $\lambda M \le (\sum_i \|a_i\|) M$, and $\lambda > \sum_i \|a_i\| \ge 0$ forces $M \le 0$. $\square$

### Hecke polynomials at a split place

Let $w$ be a finite place of $E$ split over $E^+$, with residue field $\mathbb{F}_w$ of order $q$. At $w$ the unitary group of rank $n$ is $\mathrm{GL}_n(E_w)$, and for a subspace $U$ of $\mathbb{F}_w^n$ the coset representative `New.basicCosetRep` has determinant of order $\dim U$. The Hecke polynomial of [Volume 5](/chapter/iwahori-satake/) at $w$ is
$$P_w(X) = \sum_{i \le n} (-X)^i q^{\binom{i}{2}}\, T_{w, i}$$
where $T_{w, i}$ is the Hecke operator of the subspaces of dimension $i$. Write
$$(X; q)_k = \prod_{j < k} (1 - q^j X)$$
for the $q$-Pochhammer symbol, and $c(X, U) = (-X)^{\dim U} q^{\binom{\dim U}{2}}$.

**Theorem (Hecke transfer, from Volume 5).** Let $w$ be split, let $S$ have rank $n$ and $T$ rank $m = n + k$, let the characters $a$ and $b$ be unramified at $w$, and let $f$ be a vacuum at $w$. Let $\Lambda$ be linear with $\Lambda(\omega(g, h) f) = \pi(g)\rho(h)\Lambda f$ for finite adelic $g, h$. Then $\Lambda f$ is spherical for $\pi$ and for $\rho$, and
$$P^\rho_w(X)\, \Lambda f = (\alpha X; q)_k \cdot P^\pi_{\bar w}\big(q^k \alpha \beta^{-1} X\big)\, \Lambda f,$$
where $\alpha$ and $\beta$ are the Frobenius values of $a$ and $b$ at $w$.

Lean: `New.SiegelWeil.hecke_transfer_of_equivariant`, `New.AutChar.frobValue`, `New.heckePolyOp` (Lib/Weil/Unramified/HeckeTransfer.lean; Lib/Weil/Unramified/SplitHecke.lean).

### The transfer for the pair $(S, T)$

Now let $S$ have rank $2p$ and $T$ rank $m = 2p + k$ with $p, k > 0$, and let $\upsilon(\varpi_w)$ be the splitting character at a uniformizer of $w$.

**Definition (Transfer weights and points).** For a subspace $U$ of $\mathbb{F}_w^{2p}$, the transfer weight is
$$c_U = \big(-\sqrt q^{\,2p}; q\big)_k \cdot c\Big(-\frac{q^k \sqrt q^{\,2p}}{\upsilon(\varpi_w)^{-m}\sqrt q^{\,m}},\ U\Big),$$
and the transfer point $\gamma_U \in G_S$ is the inverse of `basicCosetRep U`, placed at $w$ by `New.ofSplitPlace`, and $1$ at the other places.

Lean: `New.SiegelWeil.transferWeight`, `New.SiegelWeil.transferPoint`, `New.basicCosetRep`, `New.ofSplitPlace` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

**Theorem (The Hecke transfer at $-1$).** Let $S$ have rank $2p$ and $T$ rank $m = 2p + k$. Let $w$ be split, let $f$ satisfy $\mathrm{proj}_w f = f$, where $\mathrm{proj}_w$ is the projection on the vacua at $w$, and let $\Lambda$ be a bounded functional with $\Lambda(\omega(1, h) f') = \Lambda(f')$ for all $h \in G_T$ and all $f'$. Then for every $g \in G_S$,
$$\big\|(-1; q)_m\big\| \cdot \big\|\Lambda(\omega(g, 1) f)\big\| = \Big\| \sum_{U \le \mathbb{F}_w^{2p}} c_U\, \Lambda\big(\omega(g \gamma_U, 1) f\big) \Big\|.$$

Lean: `New.SiegelWeil.norm_qPochhammer_mul_norm_eq_norm_sum` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* Apply the Hecke transfer to $f \mapsto (g \mapsto \Lambda(\omega(g, 1) f))$. The Frobenius value of $\upsilon_1^p$ is $\sqrt q^{\,2p}$, and a vector fixed by the finite group of $T$ has Hecke polynomial $(X; q)_m$, by `New.SiegelWeil.hasHeckePolynomial_qPochhammer`. Evaluate at $X = -1$, expand the Hecke polynomial of $S$ as the sum of the translates by $\gamma_U$, and take norms. $\square$

**Theorem (An inequality of products).** Let $x > 1$ and $p, k > 0$, and put $q = x^2$. Then
$$\prod_{j < k}\big(1 + q^j x^{2p}\big) \cdot \prod_{j < 2p}\big(1 + q^j x^{k}\big) < \prod_{j < 2p + k}\big(1 + q^j\big).$$

Lean: `New.SiegelWeil.prod_mul_prod_lt_prod_one_add_pow` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* Since $q^j x^{2p} = q^{p + j}$, the first product is the middle $k$ factors of the right side. Pair the factors $j$ and $p + j$ of the second product with the factors $j$ and $p + k + j$ of the right side, for $j < p$. The two products of a pair have the same constant term and the same top term, and the difference of the middle terms is
$$q^j + q^{p+k+j} - q^j x^k - q^{p+j}x^k = x^{2j}\big(1 + x^{2p + 2k} - x^k - x^{2p + k}\big) = x^{2j}(x^k - 1)(x^{2p + k} - 1),$$
which is positive since $x > 1$. There is at least one pair since $p > 0$. $\square$

**Theorem (The total weight is small).** Let $S$ have rank $2p$, $m = 2p + k$ with $p, k > 0$. Then
$$\sum_{U \le \mathbb{F}_w^{2p}} \|c_U\| < \|(-1; q)_m\| = \prod_{l < m}(1 + q^l).$$

Lean: `New.SiegelWeil.sum_norm_transferWeight_lt`, `New.SiegelWeil.norm_transferWeight`, `New.SiegelWeil.norm_qPochhammer_neg`, `New.q_binomial_submodule`, `New.SiegelWeil.qPochhammer` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean; Lib/General/Combinatorics.lean).

*Proof.* Since $\upsilon(\varpi_w)$ has norm $1$ and $\|(-x; q)_k\| = \prod_{j < k}(1 + q^j x)$ for $x \ge 0$, $\|c_U\| = \prod_{j < k}(1 + q^j \sqrt q^{\,2p}) \cdot (\sqrt q^{\,k})^{\dim U} q^{\binom{\dim U}{2}}$. The $q$-binomial theorem over subspaces says $\sum_{U \le W} c(X, U) = (X; q)_{\dim W}$ for every subspace $W$ of $\mathbb{F}_w^{2p}$. At $W = \mathbb{F}_w^{2p}$ and $X = -\sqrt q^{\,k}$ the sum over $U$ of the last factor is $\prod_{j < 2p}(1 + q^j \sqrt q^{\,k})$. So the left side is the left side of the inequality of products for $x = \sqrt q > 1$. For $k = 0$ the two sides would be equal. $\square$

### The vacuum is a supersolution

**Theorem (The summands have one phase).** Let $w$ be split, $L$ a Lagrangian of $S$, $g \in G_S$, and $v$ the vacuum vector. There are a number $z \in \mathbb{C}$ and real numbers $r_U \ge 0$ such that for every $U$,
$$\big(\upsilon(\varpi_w)^m\big)^{\dim U}\, \mathrm{ev}_L\big(\omega(g\gamma_U, 1)v\big) = r_U\, z.$$
Consequently
$$\sum_U \|c_U\|\, \big\|\mathrm{ev}_L\big(\omega(g\gamma_U, 1)v\big)\big\| \le \Big\|\sum_U c_U\, \mathrm{ev}_L\big(\omega(g\gamma_U, 1)v\big)\Big\|.$$

Lean: `New.SiegelWeil.exists_zeroTerm_transferPoint_eq`, `New.SiegelWeil.sum_norm_mul_norm_zeroTerm_le`, `New.SiegelWeil.exists_zeroTerm_omega_schrodingerOp_eq_smul` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* The vacuum is fixed by the Schrödinger operator of the indicator of the integral box at $w$. The point $\gamma_U$ moves this indicator to a nonnegative function $\Psi_U$ times a character whose unitary part is $(\upsilon(\varpi_w)^m)^{\dim U}$, since $\upsilon$ is unramified at $w$ and the coset representative has determinant of order $\dim U$. By `exists_zeroTerm_omega_schrodingerOp_eq_smul`, the zero terms of $\omega(g)$ applied to the Schrödinger operators of nonnegative $\Psi$ are nonnegative multiples of one vector $z$. For the second claim, $c_U = c\, a_U\, (\upsilon(\varpi_w)^m)^{\dim U}$ with $a_U \ge 0$, so all summands are nonnegative multiples of $cz$. $\square$

### The vanishing criterion

**Theorem (Vanishing of dominated functionals).** Let $S$ be nonzero of rank $2p$, and let $2p < m$. Let $\ell$ be a bounded functional on $\mathcal{S}(\mathrm{Hom}(S, T))$ with:

1. $\ell(\omega(1, h) f) = \ell(f)$ for all $h \in G_T$ and all $f$;
2. for every $f$, the family $L \mapsto \mathrm{ev}_L(f)$ is summable over the Lagrangians of $S$;
3. for every $f$, the function
$$g \mapsto \big\|\ell(\omega(g, 1) f)\big\| - \sum_L \big\|\mathrm{ev}_L(\omega(g, 1) v)\big\|$$
on $G_S$ is bounded above, where $v$ is the vacuum vector.

Then $\ell(f) = 0$ for every $f$.

Lean: `New.SiegelWeil.eq_zero_of_le_tsum_zeroTerm`, `New.Space.map_eq_zero_of_map_integrated_eq_zero` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean; Lib/Weil/Construction/VacuumProjections.lean).

*Proof.* By `map_eq_zero_of_map_integrated_eq_zero` it is enough to show $\ell(\varphi) = 0$ for the vectors $\varphi$ made from the vacuum by a Fock polynomial at the infinite places and a finite Heisenberg operator $\varrho_f(z)$. Suppose $\ell(\varphi) \ne 0$, with $m = 2p + k$ and $k, p > 0$.

*Step 1.* There are infinitely many split places of prime residue order, so there is a split place $w$ with $z$ integral at $w$ and $\bar w$, and then $\mathrm{proj}_w \varphi = \varphi$.

*Step 2.* Put $\sigma(g) = \sum_L \|\mathrm{ev}_L(\omega(g, 1) v)\|$. The Hecke transfer at $-1$ for $\Lambda = \mathrm{ev}_L$, which is invariant under $G_T$ by the substitution law, and the theorem on phases give
$$\sum_U \|c_U\|\, \sigma(g\gamma_U) \le \|(-1; q)_m\|\, \sigma(g).$$

*Step 3.* Let $\mathrm{proj}_w f = f$ and $u(g) = \|\ell(\omega(g, 1) f)\| - \sigma(g)$, bounded above by hypothesis 3. The Hecke transfer at $-1$ for $\Lambda = \ell$, the triangle inequality and Step 2 give
$$\|(-1; q)_m\|\, u(g) \le \sum_U \|c_U\|\, u(g\gamma_U).$$
The total weight is less than $\|(-1; q)_m\|$, so the maximum principle gives $u \le 0$.

*Step 4.* Hypothesis 3 does not scale with $f$. Choose $\|a\| > \sigma(1)$ and apply Step 3 to $f = (a/\ell(\varphi))\varphi$ at $g = 1$: then $\|a\| \le \sigma(1)$, a contradiction. $\square$

**Remark (Formalization).** The criterion asks for summability of the zero terms for each $f$ only, and for the bound only up to an additive constant that may depend on $f$. Section 5 supplies both.
