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

The proof of the Siegel-Weil formula takes the difference $\ell$ of the two sides and shows that it is zero. This section proves the criterion for that. A functional $\ell$ on $\mathcal{S}(\mathrm{Hom}(S, T))$ that is invariant under $G_T$ is zero if, up to an additive constant, it is bounded on the translates of each vector by the Eisenstein series of the vacuum. The tool is a Hecke operator at one split place, and the argument is a maximum principle for an inequality of mean value type.

### The idea in a model case

Let $v$ be a real function on a set $X$ that is bounded above, and let $r_1, \dots, r_N$ be maps of $X$ to itself. Suppose that $\lambda v(x) \le \sum_i |a_i|\, v(r_i x)$ for all $x$, with $\sum_i |a_i| < \lambda$. At a point where $v$ is near its supremum $M$, the right side is at most $(\sum |a_i|) M$, and the left side is near $\lambda M$. If $M > 0$, this is a contradiction. So $M \le 0$. This is the discrete form of the maximum principle for a function that is subharmonic for a weighted mean with total weight less than $1$.

The Hecke operator at a split place $w$ is a weighted mean of right translates. The Hecke transfer of [Volume 5](/chapter/iwahori-satake/) says that on matrix coefficients of the Weil representation the Hecke operator of $S$ is a scalar. The scalar has absolute value larger than the total weight of the operator exactly when $2p < m$. The Eisenstein series of the vacuum satisfies the opposite inequality term by term.

### The maximum principle

**Theorem (Maximum principle).** Let $X$ be a set, $\iota$ a finite set, $v : X \to \mathbb{R}$ bounded above, $a : \iota \to \mathbb{C}$, $r : X \times \iota \to X$ and $\lambda \in \mathbb{R}$. Suppose that $\sum_{i} \|a_i\| < \lambda$ and that for all $x \in X$,
$$\lambda\, v(x) \le \sum_{i} \|a_i\|\, v(r(x, i)).$$
Then $v(x) \le 0$ for every $x \in X$.

Lean: `New.SiegelWeil.maximum_principle` (Lib/Weil/Unramified/HeckeTransfer.lean).

*Proof.* Let $x \in X$, so $X$ is not empty, and let $M = \sup v$, which is finite. Since $\lambda > \sum \|a_i\| \ge 0$, multiplication by $\lambda$ commutes with the supremum. For every $y$, $\lambda v(y) \le \sum_i \|a_i\| v(r(y, i)) \le (\sum_i \|a_i\|) M$. Taking the supremum over $y$ gives $\lambda M \le (\sum_i \|a_i\|) M$. Since $\lambda > \sum \|a_i\|$, this forces $M \le 0$, and $v(x) \le M \le 0$. $\square$

### Hecke polynomials at a split place

Let $w$ be a finite place of $E$ that is split over $E^+$, so $\bar w \neq w$, and let $q$ be the order of its residue field $\mathbb{F}_w$. At $w$ the unitary group of rank $n$ is $\mathrm{GL}_n(E_w)$. For a subspace $U$ of $\mathbb{F}_w^n$ the source fixes a representative of a double coset, `New.basicCosetRep`, of determinant of order $\dim U$. The Hecke polynomial of [Volume 5](/chapter/iwahori-satake/) at $w$ is the family of operators
$$P_w(X) = \sum_{i \le n} (-X)^i q^{\binom{i}{2}}\, T_{w, i}$$
on spherical vectors, where $T_{w, i}$ is the Hecke operator of the subspaces of dimension $i$. Write
$$(X; q)_k = \prod_{j < k} (1 - q^j X)$$
for the $q$-Pochhammer symbol, and $c(X, U) = (-X)^{\dim U} q^{\binom{\dim U}{2}}$.

**Theorem (The $q$-binomial theorem over subspaces).** For a finite field $k$ with $q$ elements, a subspace $W \le k^n$ and $X \in \mathbb{C}$,
$$\sum_{U \le W} c(X, U) = (X; q)_{\dim W}.$$

Lean: `New.q_binomial_submodule`, `New.SiegelWeil.qPochhammer`, `New.heckePolyCoeff` (Lib/General/Combinatorics.lean).

**Theorem (Hecke transfer, from Volume 5).** Let $w$ be split, let $S$ have rank $n$ and $T$ rank $m = n + k$, let the characters $a$ and $b$ be unramified at $w$, and let $f$ be a vacuum at $w$. Let $\Lambda$ be linear with $\Lambda(\omega(g, h) f) = \pi(g)\rho(h)\Lambda f$ for finite adelic $g, h$. Then $\Lambda f$ is spherical for $\pi$ and for $\rho$, and
$$P^\rho_w(X)\, \Lambda f = (\alpha X; q)_k \cdot P^\pi_{\bar w}\big(q^k \alpha \beta^{-1} X\big)\, \Lambda f,$$
where $\alpha$ and $\beta$ are the Frobenius values of $a$ and $b$ at $w$.

Lean: `New.SiegelWeil.hecke_transfer_of_equivariant`, `New.AutChar.frobValue`, `New.heckePolyOp` (Lib/Weil/Unramified/HeckeTransfer.lean; Lib/Weil/Unramified/SplitHecke.lean).

### The transfer for the pair $(S, T)$

Now let $S$ have rank $2p$ and $T$ rank $m = 2p + k$ with $p, k > 0$. Write $\upsilon(\varpi_w)$ for the value of the splitting character at a uniformizer of $w$.

**Definition (Transfer weights and points).** For a subspace $U$ of $\mathbb{F}_w^{2p}$, the transfer weight is
$$c_U = \big(-\sqrt q^{\,2p}; q\big)_k \cdot c\Big(-\frac{q^k \sqrt q^{\,2p}}{\upsilon(\varpi_w)^{-m}\sqrt q^{\,m}},\ U\Big),$$
and the transfer point $\gamma_U \in G_S$ is the inverse of `basicCosetRep U`, placed at $w$ by `New.ofSplitPlace`, and $1$ at the other places.

Lean: `New.SiegelWeil.transferWeight`, `New.SiegelWeil.transferPoint`, `New.basicCosetRep`, `New.ofSplitPlace` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

**Theorem (The Hecke transfer at $-1$).** Let $S$ have rank $2p$ and $T$ rank $m = 2p + k$. Let $w$ be split, let $f$ satisfy $\mathrm{proj}_w f = f$, where $\mathrm{proj}_w$ is the projection on the vacua at $w$, and let $\Lambda$ be a bounded functional with $\Lambda(\omega(1, h) f') = \Lambda(f')$ for all $h \in G_T$ and all $f'$. Then for every $g \in G_S$,
$$\big\|(-1; q)_m\big\| \cdot \big\|\Lambda(\omega(g, 1) f)\big\| = \Big\| \sum_{U \le \mathbb{F}_w^{2p}} c_U\, \Lambda\big(\omega(g \gamma_U, 1) f\big) \Big\|.$$

Lean: `New.SiegelWeil.norm_qPochhammer_mul_norm_eq_norm_sum` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* Apply the Hecke transfer to the linear map $f \mapsto (g \mapsto \Lambda(\omega(g, 1) f))$ into functions on $G_S$. The group of $S$ acts on such functions by right translation, and the group of $T$ acts trivially, since $\Lambda$ is invariant. The Frobenius value of the character $\upsilon_1^p$ is $\sqrt q^{\,2p}$. On the side of $T$, a vector fixed by the finite group has Hecke polynomial $(X; q)_m$, by `New.SiegelWeil.hasHeckePolynomial_qPochhammer`. Evaluate the identity at $X = -1$. The left side becomes $(-1; q)_m \Lambda(\omega(g,1)f)$, and the right side is $(-\sqrt q^{\,2p}; q)_k$ times the Hecke polynomial of $S$ at the point that the definition of $c_U$ records. Expand the Hecke polynomial of $S$ as the sum over $U$ of the translates by $\gamma_U$. Take norms. $\square$

The point is the comparison of total weights. The norms are as follows.

**Theorem (The norms of the weights).** For $x \ge 0$, $\|(-x; q)_k\| = \prod_{j < k}(1 + q^j x)$. With $m = 2p + k$,
$$\|c_U\| = \prod_{j < k}\big(1 + q^j \sqrt q^{\,2p}\big) \cdot \big(\sqrt q^{\,k}\big)^{\dim U} q^{\binom{\dim U}{2}}.$$

Lean: `New.SiegelWeil.norm_qPochhammer_neg`, `New.SiegelWeil.norm_transferWeight` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* For $x \ge 0$ each factor $1 + q^j x$ is a positive real number. For the weight, $\upsilon(\varpi_w)$ has norm $1$, and $q^k \sqrt q^{\,2p}/\sqrt q^{\,2p + k} = \sqrt q^{\,k}$ since $q = \sqrt q^{\,2}$. $\square$

**Theorem (An inequality of products).** Let $x > 1$ and $p, k > 0$, and put $q = x^2$. Then
$$\prod_{j < k}\big(1 + q^j x^{2p}\big) \cdot \prod_{j < 2p}\big(1 + q^j x^{k}\big) < \prod_{j < 2p + k}\big(1 + q^j\big).$$

Lean: `New.SiegelWeil.prod_mul_prod_lt_prod_one_add_pow` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* Since $q^j x^{2p} = q^{p + j}$, the first product is $\prod_{j < k}(1 + q^{p + j})$, the middle $k$ factors of the right side. Split the second product into the factors $j$ and $p + j$ for $j < p$, and split the right side into the middle factors and the pairs $(j, p + k + j)$ for $j < p$. It is enough to show for each $j < p$ that
$$(1 + q^j x^k)(1 + q^{p+j} x^k) < (1 + q^j)(1 + q^{p+k+j}).$$
Both sides have the constant term $1$, and the products of the two terms are equal, since $q^j x^k \cdot q^{p+j} x^k = q^{p + k + 2j} = q^j q^{p + k + j}$. The difference of the right and the left side is the difference of the middle terms,
$$q^j + q^{p+k+j} - q^j x^k - q^{p+j}x^k = x^{2j}\big(1 + x^{2p + 2k} - x^k - x^{2p + k}\big) = x^{2j}(x^k - 1)(x^{2p + k} - 1),$$
which is positive since $x > 1$. The product over $j < p$ is not empty since $p > 0$. $\square$

**Theorem (The total weight is small).** Let $S$ have rank $2p$, $m = 2p + k$ with $p, k > 0$. Then
$$\sum_{U \le \mathbb{F}_w^{2p}} \|c_U\| < \|(-1; q)_m\| = \prod_{l < m}(1 + q^l).$$

Lean: `New.SiegelWeil.sum_norm_transferWeight_lt` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* By the $q$-binomial theorem at $X = -\sqrt q^{\,k}$, the sum of $(\sqrt q^{\,k})^{\dim U} q^{\binom{\dim U}{2}}$ over the subspaces is $\prod_{j < 2p}(1 + q^j \sqrt q^{\,k})$. So the left side is the left side of the inequality of products for $x = \sqrt q > 1$. $\square$

This is where the hypothesis $k > 0$, that is $2p < m$, enters the vanishing argument. For $k = 0$ the two sides would be equal.

### The vacuum is a supersolution

The second ingredient is that the Eisenstein series of the vacuum satisfies the inequality of the maximum principle with the opposite sign. This needs a fact on phases.

**Theorem (The summands have one phase).** Let $w$ be split, $L$ a Lagrangian of $S$, $g \in G_S$, and $v$ the vacuum vector. There are a number $z \in \mathbb{C}$ and real numbers $r_U \ge 0$ such that for every $U$,
$$\big(\upsilon(\varpi_w)^m\big)^{\dim U}\, \mathrm{ev}_L\big(\omega(g\gamma_U, 1)v\big) = r_U\, z.$$
Consequently
$$\sum_U \|c_U\|\, \big\|\mathrm{ev}_L\big(\omega(g\gamma_U, 1)v\big)\big\| \le \Big\|\sum_U c_U\, \mathrm{ev}_L\big(\omega(g\gamma_U, 1)v\big)\Big\|.$$

Lean: `New.SiegelWeil.exists_zeroTerm_transferPoint_eq`, `New.SiegelWeil.sum_norm_mul_norm_zeroTerm_le`, `New.SiegelWeil.exists_zeroTerm_omega_schrodingerOp_eq_smul` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean).

*Proof.* The vacuum is fixed by the Schrödinger operator of the indicator of the integral box at $w$. The point $\gamma_U$, read in the group of $\mathrm{Hom}(S, T)$, is a finite element $\kappa$ above $w$, and it moves this indicator to a new nonnegative function $\Psi_U$ times a character of $\det \kappa$. The unitary part of that character is $\upsilon(\det\kappa) = (\upsilon(\varpi_w)^m)^{\dim U}$, because $\upsilon$ is unramified at $w$ and the determinant of the coset representative has order $\dim U$. By `exists_zeroTerm_omega_schrodingerOp_eq_smul`, as $\Psi$ runs over the nonnegative Schwartz-Bruhat functions above $w$, the zero terms of $\omega(g)$ applied to the Schrödinger operator of $\Psi$ are nonnegative multiples of one vector. This gives $r_U$ and $z$. For the second claim, $c_U = c\, a_U\, (\upsilon(\varpi_w)^m)^{\dim U}$ with $c = (-\sqrt q^{\,2p}; q)_k$ and $a_U \ge 0$. So every summand is a nonnegative real multiple of $cz$, and the norm of the sum is the sum of the norms. $\square$

### The vanishing criterion

**Theorem (Vanishing of dominated functionals).** Let $S$ be nonzero of rank $2p$, and let $2p < m$. Let $\ell$ be a bounded functional on $\mathcal{S}(\mathrm{Hom}(S, T))$ with:

1. $\ell(\omega(1, h) f) = \ell(f)$ for all $h \in G_T$ and all $f$;
2. for every $f$, the family $L \mapsto \mathrm{ev}_L(f)$ is summable over the Lagrangians of $S$;
3. for every $f$, the function
$$g \mapsto \big\|\ell(\omega(g, 1) f)\big\| - \sum_L \big\|\mathrm{ev}_L(\omega(g, 1) v)\big\|$$
on $G_S$ is bounded above, where $v$ is the vacuum vector.

Then $\ell(f) = 0$ for every $f$.

Lean: `New.SiegelWeil.eq_zero_of_le_tsum_zeroTerm`, `New.Space.map_eq_zero_of_map_integrated_eq_zero` (Lib/SiegelWeil/Formula/LagrangianZeroTerms.lean; Lib/Weil/Construction/VacuumProjections.lean).

*Proof.* By `map_eq_zero_of_map_integrated_eq_zero` of the vacuum projections, it is enough to show $\ell(\varphi) = 0$ for the vectors $\varphi$ obtained from the vacuum by a polynomial vector of the Fock space at the infinite places and a finite Heisenberg operator $\varrho_f(z)$. Fix such a $\varphi$ and suppose that $\ell(\varphi) \ne 0$. Write $m = 2p + k$ with $k > 0$, and note that $p > 0$ since $S \ne 0$.

*Step 1: a split place.* Infinitely many finite places have a residue field of prime order, and these are split. The finite adele $z$ is integral at almost all places. So there is a split place $w$ with $z$ integral at $w$ and at $\bar w$. Then $\mathrm{proj}_w \varphi = \varphi$.

*Step 2: the supersolution.* Put $\sigma(g) = \sum_L \|\mathrm{ev}_L(\omega(g, 1) v)\|$. Each zero term is invariant under $G_T$, by the substitution law. Apply the Hecke transfer at $-1$ to $\Lambda = \mathrm{ev}_L$ and $f = v$, which is a vacuum at $w$, and combine it with the theorem on phases. This gives, term by term in $L$,
$$\sum_U \|c_U\|\, \sigma(g\gamma_U) \le \|(-1; q)_m\|\, \sigma(g).$$

*Step 3: the maximum principle.* Let $f$ satisfy $\mathrm{proj}_w f = f$. Put $u(g) = \|\ell(\omega(g, 1) f)\| - \sigma(g)$, which is bounded above by hypothesis 3. The Hecke transfer at $-1$ for $\Lambda = \ell$ and the triangle inequality give $\|(-1;q)_m\| \|\ell(\omega(g,1)f)\| \le \sum_U \|c_U\|\, \|\ell(\omega(g\gamma_U, 1) f)\|$. Subtract the inequality of Step 2:
$$\|(-1; q)_m\|\, u(g) \le \sum_U \|c_U\|\, u(g\gamma_U).$$
The total weight is less than $\|(-1; q)_m\|$. The maximum principle gives $u(g) \le 0$ for all $g$.

*Step 4: scaling.* Choose $a \in \mathbb{C}$ with $\|a\| > \sigma(1)$, and apply Step 3 to $f = (a/\ell(\varphi))\varphi$ at $g = 1$. Then $\|a\| - \sigma(1) \le 0$, a contradiction. So $\ell(\varphi) = 0$. $\square$

The scaling in Step 4 is the reason the bound in hypothesis 3 uses the vacuum and not $f$: the right side does not change when $f$ is multiplied by a scalar, so a functional with $\ell \ne 0$ cannot satisfy it for all multiples.

**Remark (Formalization).** The criterion asks for summability of the zero terms only for each $f$ and for the bound only up to an additive constant that may depend on $f$. Section 5 supplies both from the convergence theorems of Section 3 and from the induction. The criterion is part of the method that the docstring of `New.SiegelWeil.siegel_weil` attributes to Andrianov, Harris and Garrett.
