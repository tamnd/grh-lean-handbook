---
title: Roots of unity
lean:
  - New/Congruences/Selmer/RootsOfUnity.lean
decls:
  - New.Selmer.rootRadius
  - New.Selmer.ellVal_sub_one_eq_rootRadius
  - New.Selmer.radiusExponents
  - New.Selmer.exists_lt_mul_sum_radiusExponents
  - New.Selmer.rootsOfValuation
  - New.Selmer.ellVal_eval_add_card_mul
  - New.Selmer.sum_card_rootsOfValuation_mul_le
  - New.Selmer.exists_card_rootsOfValuation_mul_le
  - New.Selmer.sum_min_ellVal_sub_le
  - New.Selmer.exists_sum_min_ellVal_sub_le
  - New.Selmer.exists_rootOfUnity_eval_le_gaussVal_add
  - New.Selmer.exists_ellVal_eval_update_le_add
  - New.Selmer.exists_ellVal_eval_piecewise_le_add
  - New.Selmer.exists_rootsOfUnity_ellVal_eval_le_add
status: drafted
drafted_by: writer@claude-opus-5-5
---

## Roots of unity

The twist polynomials of the last section are small at points $x$ near $0$. A twist needs a point of the form $x = (\zeta_j - 1)_j$ with $\zeta_j$ roots of unity. This section moves the points to such roots and loses at most $\varepsilon$ in each valuation. The orders of the roots are bounded before the polynomials are given. All results are in [RootsOfUnity.lean](lean:New/Congruences/Selmer/RootsOfUnity.lean#L1).

Background: the Gauss valuation $v_\rho(g) = \min_i (v(y_i) + \rho i)$ of $g = \sum y_i Y^i$ over $\bar{\mathbb{Z}}_\ell$ is additive on products, has $v(g(y)) \geq v_\rho(g)$ if $v(y) \geq \rho$, and increases with $\rho$ ([the other tools](/chapter/fitting-ideals/#the-other-tools)). With the integral roots $\alpha$ of $g$, counted with multiplicity, $v_\rho(g) = v_0(g) + \sum_\alpha \min(v(\alpha), \rho)$ and $v(g(y)) = v_0(g) + \sum_\alpha v(y - \alpha)$ for integral $y$ (`New.Selmer.gaussVal_eq_add_sum_roots`, `New.Selmer.ellVal_eval_eq_add_sum_roots`, Lib/General/NumberTheory/GaussValuation.lean).

### Radii and the harmonic series

**Definition.** For $h \geq 0$ put $\rho_h = 1/\varphi(\ell^h)$ (`rootRadius`). For $\rho > 0$ and $h_0$, let $H(\rho, h_0)$ be the set of $h$ with $1 \leq h \leq h_0$ and $\rho_h \leq \rho$ (`radiusExponents`). For $g$ over $\bar{\mathbb{Z}}_\ell$ and $r$, let $R(g, r)$ be the multiset of the integral roots of $g$ of valuation $r$ (`rootsOfValuation`).

Lean: `New.Selmer.rootRadius`, `New.Selmer.radiusExponents`, `New.Selmer.rootsOfValuation` (New/Congruences/Selmer/RootsOfUnity.lean).

**Lemma.**

1. If $h \geq 1$ and $\zeta$ is a primitive $\ell^h$-th root of unity, then $v(\zeta - 1) = \rho_h$.
2. For $\rho > 0$, $\delta > 0$ and $B$, there is $h_0$ with $B < \delta \sum_{h \in H(\rho, h_0)} 1/(h + 1)$.

Lean: `New.Selmer.ellVal_sub_one_eq_rootRadius`, `New.Selmer.exists_lt_mul_sum_radiusExponents` (New/Congruences/Selmer/RootsOfUnity.lean).

*Proof.* (1) $\zeta - 1$ is a root of the Eisenstein polynomial $\Phi_{\ell^h}(1 + Y)$ of degree $\varphi(\ell^h)$ with constant term $\ell$. (2) Since $\rho_h \to 0$, there is $N$ with $1 \leq h$ and $\rho_h \leq \rho$ for all $h \geq N$. The harmonic series diverges, so for large $h_0$ the sum of $1/(h + 1)$ over $N \leq h < h_0$ exceeds $B/\delta$. These $h$ lie in $H(\rho, h_0)$. $\square$

### One variable

**Lemma (Roots at one radius).** Let $g$ be a polynomial over $\bar{\mathbb{Z}}_\ell$.

1. If $v(y) = r$, then $v(g(y)) + \# R(g, r) \cdot r = v_r(g) + \sum_{\alpha \in R(g, r)} v(y - \alpha)$.
2. $\sum_{h \in H(\rho, h_0)} \# R(g, \rho_h)\, \rho_h \leq v_\rho(g)$.
3. If $v_\rho(g) \leq B < \delta \sum_{h \in H(\rho, h_0)} 1/(h + 1)$, then some $h \in H(\rho, h_0)$ has $\# R(g, \rho_h)\, \rho_h \leq \delta/(h + 1)$.

Lean: `New.Selmer.ellVal_eval_add_card_mul`, `New.Selmer.sum_card_rootsOfValuation_mul_le`, `New.Selmer.exists_card_rootsOfValuation_mul_le` (New/Congruences/Selmer/RootsOfUnity.lean).

*Proof.* (1) Split the integral roots into $R = R(g, r)$ and the rest $R'$. For $\alpha \in R'$, $v(\alpha) \neq v(y)$, so $v(y - \alpha) = \min(v(\alpha), r)$. For $\alpha \in R$, $\min(v(\alpha), r) = r$. Put these into the two root formulas of the background and compare.

(2) In the root formula for $v_\rho(g)$, a root $\alpha$ contributes $\min(v(\alpha), \rho)$. The radii $\rho_h$ with $h \geq 1$ are distinct, so $\alpha$ lies in $R(g, \rho_h)$ for at most one $h \in H(\rho, h_0)$. For that $h$ its contribution is $\rho_h$. The term $v_0(g)$ is not negative.

(3) Otherwise every $h$ has $\# R(g, \rho_h)\, \rho_h > \delta/(h + 1)$. Summing and using (2) gives $\delta \sum 1/(h + 1) \leq v_\rho(g) \leq B$, which is false. $\square$

**Lemma (Few close roots of unity).** Let $1 + \alpha$ be a unit of $\bar{\mathbb{Z}}_\ell$.

1. $\sum_\zeta \min(v(\zeta - 1 - \alpha), 1) \leq h + 1$, over the primitive $\ell^h$-th roots of unity $\zeta$.
2. Let $R$ be a multiset with $1 + \alpha$ a unit for all $\alpha \in R$. Some primitive $\ell^h$-th root of unity $\zeta$ has $\sum_{\alpha \in R} \min(v(\zeta - 1 - \alpha), 1) \leq \# R\, \rho_h (h + 1)$.

Lean: `New.Selmer.sum_min_ellVal_sub_le`, `New.Selmer.exists_sum_min_ellVal_sub_le` (New/Congruences/Selmer/RootsOfUnity.lean).

*Proof.* (1) Put $f = (Y + 1 + \alpha)^{\ell^h} - 1$. The numbers $\zeta - 1 - \alpha$ are distinct roots of $f$. The coefficient of $Y$ in $f$ is $\ell^h (1 + \alpha)^{\ell^h - 1}$, of valuation $h$. So $f \neq 0$ and $v_1(f) \leq h + 1$. The root formula gives $\sum_\zeta \min(v(\zeta - 1 - \alpha), 1) \leq v_1(f)$.

(2) There are $\varphi(\ell^h) = 1/\rho_h$ primitive roots. Sum the bound (1) over $\alpha \in R$ and exchange the sums. The total over all $\zeta$ is at most $\# R (h + 1)$. So some $\zeta$ has at most the average $\# R (h + 1) \rho_h$. $\square$

**Theorem (One variable).** Let $\delta < 1$, $B < \delta \sum_{h \in H(\rho, h_0)} 1/(h + 1)$ and $v_\rho(g) \leq B$. There are $h \in H(\rho, h_0)$ and a primitive $\ell^h$-th root of unity $\zeta$ with $v(g(\zeta - 1)) \leq v_{\rho_h}(g) + \delta$.

Lean: `New.Selmer.exists_rootOfUnity_eval_le_gaussVal_add` (New/Congruences/Selmer/RootsOfUnity.lean).

*Proof.* Choose $h$ by part 3 of the lemma on roots at one radius, and let $R = R(g, \rho_h)$. Each $\alpha \in R$ has $v(\alpha) = \rho_h > 0$, so $1 + \alpha$ is a unit. Choose $\zeta$ by part 2 of the last lemma: the sum of the $\min(v(\zeta - 1 - \alpha), 1)$ is at most $\# R \rho_h (h + 1) \leq \delta$. Since $\delta < 1$, no term reaches $1$, so each minimum is $v(\zeta - 1 - \alpha)$. Part 1 of the lemma on roots at one radius, with $y = \zeta - 1$ and $r = \rho_h$, gives

$$v(g(\zeta - 1)) \leq v(g(\zeta - 1)) + \# R\, \rho_h = v_{\rho_h}(g) + \sum_{\alpha \in R} v(\zeta - 1 - \alpha) \leq v_{\rho_h}(g) + \delta. \ \square$$

### Several variables

**Lemma (One coordinate).** Let $\delta < 1$ and $B < \delta \sum_{h \in H(\rho, h_0)} 1/(h + 1)$. Let $P_i$ be finitely many polynomials over $\bar{\mathbb{Z}}_\ell$, $x_i$ points, $j$ a coordinate with $v(x_{i,j}) \geq \rho$ for all $i$, and $\sum_i v(P_i(x_i)) \leq B$. There is $\zeta$ with $\zeta^{\ell^{h_0}} = 1$ and $v(\zeta - 1) \leq \rho$ such that replacing $x_{i,j}$ by $\zeta - 1$ in every $x_i$ raises each $v(P_i(x_i))$, and also their sum, by at most $\delta$.

Lean: `New.Selmer.exists_ellVal_eval_update_le_add` (New/Congruences/Selmer/RootsOfUnity.lean).

*Proof.* Let $g_i(Y)$ be $P_i$ at $x_i$ with $Y$ in the coordinate $j$ (`freeCoordinate`). Then $v_\rho(g_i) \leq v(P_i(x_i))$, as $v(x_{i,j}) \geq \rho$. So $v_\rho(\prod_i g_i) \leq B$. The theorem in one variable gives $h$ and $\zeta$ of order $\ell^h$ with $v(\prod_i g_i(\zeta - 1)) \leq \sum_i v_{\rho_h}(g_i) + \delta$. Then $\zeta^{\ell^{h_0}} = 1$ since $h \leq h_0$, and $v(\zeta - 1) = \rho_h \leq \rho$. Each $v(g_i(\zeta - 1)) \geq v_{\rho_h}(g_i)$, and the sum of the $v_{\rho_h}(g_i)$ is finite. So each term exceeds its lower bound by at most $\delta$: $v(g_i(\zeta - 1)) \leq v_{\rho_h}(g_i) + \delta$ (`New.Selmer.le_add_of_sum_le_sum_add`). Finally $v_{\rho_h}(g_i) \leq v_\rho(g_i) \leq v(P_i(x_i))$, since $\rho_h \leq \rho$. $\square$

**Lemma (A set of coordinates).** Let $\delta < 1$, $\# \sigma \cdot \delta \leq 1$ and $\beta + 1 < \delta \sum_{h \in H(\rho, h_0)} 1/(h + 1)$. Let $v(x_{i,j}) \geq \rho$ for all $i$, $j$ and $\sum_i v(P_i(x_i)) \leq \beta$. For each finite set $t$ of coordinates there are $\zeta_j$, $j \in t$, with $\zeta_j^{\ell^{h_0}} = 1$ and $v(\zeta_j - 1) \leq \rho$, such that replacing $x_{i,j}$ by $\zeta_j - 1$ for $j \in t$ raises each $v(P_i(x_i))$ by at most $\# t\, \delta$, and the sum stays at most $\beta + \# t\, \delta$.

Lean: `New.Selmer.exists_ellVal_eval_piecewise_le_add` (New/Congruences/Selmer/RootsOfUnity.lean).

*Proof.* Induction on $t$. For $t = \emptyset$ take nothing. For $t \cup \{j\}$ with $j \notin t$, the induction gives points $y_i$ with the coordinates in $t$ moved and $\sum_i v(P_i(y_i)) \leq \beta + \# t\, \delta \leq \beta + 1$. The coordinate $j$ of $y_i$ is still $x_{i,j}$. The lemma on one coordinate with $B = \beta + 1$ moves it with a further loss $\delta$. $\square$

**Theorem (Roots of unity).** Let $s_0 \in \mathbb{N}$, $\rho > 0$, $\beta \geq 0$ and $\varepsilon > 0$. There is $h_0$ with this property. Let $P_i$ be finitely many polynomials over $\bar{\mathbb{Z}}_\ell$ in at most $s_0$ variables, and $x_i$ points with all coordinates of valuation at least $\rho$ and $\sum_i v(P_i(x_i)) \leq \beta$. There are $\zeta_j$ with $\zeta_j^{\ell^{h_0}} = 1$ and $v(\zeta_j - 1) \leq \rho$ such that $v(P_i((\zeta_j - 1)_j)) \leq v(P_i(x_i)) + \varepsilon$ for all $i$.

Lean: `New.Selmer.exists_rootsOfUnity_ellVal_eval_le_add` (New/Congruences/Selmer/RootsOfUnity.lean).

*Proof.* Put $\delta = \min(\varepsilon, 1)/(s_0 + 2)$. Then $0 < \delta < 1$. Take $h_0$ from the harmonic lemma with $B = \beta + 1$. Given the $P_i$ and $x_i$ in $\#\sigma \leq s_0$ variables, $\#\sigma\, \delta \leq (s_0 + 2) \delta = \min(\varepsilon, 1) \leq 1$. The lemma on a set of coordinates with $t = \sigma$ moves all coordinates with a loss of at most $\#\sigma\, \delta \leq \varepsilon$. $\square$

**Remark (Formalization).** The bound $h_0$ depends on $s_0$, $\rho$, $\beta$ and $\varepsilon$ only. It does not depend on the degrees of the $P_i$ or on their number. The source compares this with a degree free bound for one element in the literature; see the notes.
