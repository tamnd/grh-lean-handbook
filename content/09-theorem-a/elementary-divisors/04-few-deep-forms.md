---
title: Few deep forms
lean:
  - Lib/General/Algebra/MultivariatePolynomials.lean
  - New/UpperBound/ElementaryDivisors/Depth.lean
  - New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean
decls:
  - New.exists_le_weight_of_mem_vanishingIdeal_pow
  - New.FrobeniusCycle.deepOrder
  - New.FrobeniusCycle.prod_deepOrder_le
  - New.FrobeniusCycle.exists_le_weight_of_mem_deepForms
  - New.finrank_le_card_of_forall_exists_ne_zero
  - New.mul_sum_exponentOf
  - New.FrobeniusCycle.sum_deepIndicator_div_le
  - New.FrobeniusCycle.sum_finrank_deepForms_le
  - New.FrobeniusCycle.IsLargeDegree.exists_basis_det_dvd
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Few deep forms

The colength of Section 3 is $w^l$ with $l = |X|\sum_{\delta < x}\dim\mathrm{deepForms}(\delta + 1)$, computed over the residue field of $O$, which has characteristic $p$. This section bounds the sum by $c_{\mathrm{div}}|\mathrm{Exp}|$. The idea is the Combinatorial Nullstellensatz with multiplicity: a deep form vanishes to high order at many points, so it must have a monomial of large weighted degree, and the mean weighted degree of all monomials is small.

### The Nullstellensatz with multiplicity

The textbook form is due to Alon (Combinatorial Nullstellensatz, Combinatorics, Probability and Computing 8 (1999), Theorem 1.2): if $f$ has degree $\sum_u t_u$ and the coefficient of $\prod_u x_u^{t_u}$ is nonzero, then $f$ does not vanish on a grid $\prod_u S_u$ with $|S_u| > t_u$. Ball and Serra proved versions with multiplicity (Punctured combinatorial Nullstellensätze, Combinatorica 29 (2009)). The source needs a version for sets that are not grids. The grid is replaced by equations $x_u^{\kappa_u} = g_u$ that hold at all points, with $g_u$ of lower cost.

**Theorem (Nullstellensatz with multiplicity).** Let $K$ be a field, $\iota$ a finite set of variables and $\kappa : \iota \to \mathbb N$ with all $\kappa_u > 0$. Give $x_u$ the cost $1/\kappa_u$; the cost of a monomial is its weighted degree. Let $z_t$, $t \in S$, be distinct points of $K^\iota$ with $\prod_u\kappa_u \le |S|$. Let $g_u$ be polynomials all of whose monomials cost less than $1$, with $g_u(z_t) = (z_t)_u^{\kappa_u}$ for all $u$, $t$. Let $d \in \mathbb N$ and $f \ne 0$ with $f \in \mathfrak m_{z_t}^d$ for every $t$. Then $f$ has a monomial of cost at least $d$.

Lean: `New.exists_le_weight_of_mem_vanishingIdeal_pow` (Lib/General/Algebra/MultivariatePolynomials.lean).

*Proof.* Put $\psi_u = x_u^{\kappa_u} - g_u$; it vanishes at every point. Let $\Gamma$ be the exponents $\gamma$ of total degree below $d$, and consider the products $b_{\alpha\gamma} = x^\alpha\psi^\gamma$ with $\alpha < \kappa$ (that is, $\alpha_u < \kappa_u$ for all $u$) and $\gamma \in \Gamma$.

*Reduction.* Every monomial $x^\alpha\psi^\gamma$ with $\mathrm{cost}(\alpha) + |\gamma| < d$ lies in the span of the $b_{\alpha'\gamma'}$ with $\alpha' < \kappa$, $\gamma' \in \Gamma$. Induct on $\alpha$ along a well founded order. If $\alpha < \kappa$, it is a $b$. Otherwise $\alpha = \kappa_u e_u + \beta$ for some $u$, and $x^{\kappa_u} = \psi_u + g_u$ gives $x^\alpha\psi^\gamma = x^\beta\psi^{\gamma + e_u} + g_ux^\beta\psi^\gamma$. The first term has cost $\mathrm{cost}(\beta) + |\gamma| + 1 = \mathrm{cost}(\alpha) + |\gamma|$, and the monomials $x^\delta$ of $g_u$ give terms $x^{\delta + \beta}\psi^\gamma$ of cost below $1 + \mathrm{cost}(\beta) = \mathrm{cost}(\alpha)$. Both are covered by the induction.

*Count.* Let $\mathcal J$ be the map that sends a polynomial to its jets of order below $d$ at all points, that is, the coefficients of $x^\gamma$, $\gamma \in \Gamma$, after translating $z_t$ to $0$. It is onto $K^{S\times\Gamma}$, as the points are distinct. The $\psi^\gamma$ with $|\gamma| = d$ lie in its kernel, so the $b_{\alpha\gamma}$ span modulo the kernel. Their number is $\prod_u\kappa_u\cdot|\Gamma| \le |S||\Gamma|$, the dimension of the target. So their images under $\mathcal J$ are independent.

*Conclusion.* If every monomial of $f$ cost less than $d$, the reduction would write $f = \sum c_{\alpha\gamma}b_{\alpha\gamma}$. As $\mathcal J(f) = 0$, all $c_{\alpha\gamma}$ vanish, and $f = 0$. $\square$

### The points and the orders

Write $k = 2r + m$, which is possible since $2r \le k$. The points are the unipotent matrices $1 + A$ with $A$ supported in the $r(m+1)$ positions $(a, c)$, $a < r$, where $c = a + r$ or $c \ge 2r$. There are $q^{r(m+1)}$ families of residues $y$ at these positions.

**Definition (Deep order).** For the variable $v = (b, s)$, $\kappa_v = P^{2r}$ if $v$ is deep and $b \ge 2r$, $\kappa_v = P$ if $v$ is deep and $b < 2r$, and $\kappa_v = 1$ if $v$ is not deep.

Lean: `New.FrobeniusCycle.deepOrder` (New/UpperBound/ElementaryDivisors/Depth.lean).

**Lemma.** If $k = 2r + m$, then $\prod_v\kappa_v \le q^{r(m+1)}$.

Lean: `New.FrobeniusCycle.prod_deepOrder_le` (New/UpperBound/ElementaryDivisors/Depth.lean).

*Proof.* Each index $b$ is deep in exactly $N/2$ letters, as the parities alternate. The $2r$ indices $b < 2r$ give the exponent $2r\cdot N/2$ of $P$, and the $m$ indices $b \ge 2r$ give $m\cdot (N/2)\cdot 2r$. The total exponent is $(N/2)\cdot 2\cdot r(m+1) \le Nr(m+1)$, and $P^N = q$. $\square$

**Theorem (Deep forms have a costly monomial).** Let $K$ be a field of characteristic $p$, $T$ a Frobenius cycle over $W$ and $K$, and $2r \le k$. Let $F \ne 0$ lie in $\mathrm{deepForms}(k, n, r, \tau)$. Then $F_\beta \ne 0$ for some $\beta$ with

$$\tau \le \sum_v \beta(v)\,\frac{\epsilon_r(v)}{P^{\,2r\ \text{if}\ b \ge 2r,\ \text{else}\ 1}},$$

where $\epsilon_r(v) \in \{0, 1\}$ is the deep indicator.

Lean: `New.FrobeniusCycle.exists_le_weight_of_mem_deepForms` (New/UpperBound/ElementaryDivisors/Depth.lean).

*Proof.* Let $L$ be the field of fractions of the polynomial ring over $K$ in all variables. Read $F$ as a polynomial $f$ in the deep variables, with the shallow variables as coefficients in $L$. For a family $y$ of residues, the point $z(y)$ has at the deep variable $(b, s)$ a coordinate that is a linear form in the $\iota_s(\tilde y_t)$, for lifts $\tilde y_t$ of $y_t$, with coefficients that are shallow variables up to sign (`New.FrobeniusCycle.entryFormValue`). The points are distinct (`New.FrobeniusCycle.entryFormValue_injective`). A translate of $F$ by $(1 + A)^{-1}$ has only monomials of depth at least $\tau$, and this translate is $f$ moved to $z(y)$; so $f$ vanishes to order $\tau$ at $z(y)$ (`New.FrobeniusCycle.specializeShallow_polyOfCoeffs_mem_vanishingIdeal_pow`). In characteristic $p$, $\iota_{s+j}(x) = \iota_s(x)^{P^j}$ exactly, so for $\kappa_v = P^j$ the power $z(y)_v^{P^j}$ is a linear form in the $\iota_{s+j}(\tilde y_t)$. Such linear forms are values of polynomials in the coordinates of $z(y)$ of cost below $1$ (`New.FrobeniusCycle.exists_eval_entryFormValue_eq_pow_deepOrder`). With the lemma on $\prod\kappa_v$, the Nullstellensatz gives a monomial $\alpha$ of $f$ of cost at least $\tau$. This $\alpha$ is the deep part of some $\beta$ with $F_\beta \ne 0$, and its cost is the weight in the statement. $\square$

### The dimension count

**Lemma.** If every nonzero $F$ in a subspace $S \subseteq K^\iota$ is nonzero somewhere on a finite set $s$, then $\dim S \le |s|$.

Lean: `New.finrank_le_card_of_forall_exists_ne_zero` (New/UpperBound/ElementaryDivisors/Depth.lean).

*Proof.* Restriction to $s$ is injective on $S$. $\square$

**Lemma.** For every variable $x$, $k\sum_{\beta\in\mathrm{Exp}}\beta(x) = |\mathrm{Mon}(k, n)|^N\,n$, where $\mathrm{Mon}(k,n)$ is the set of monomials of degree $n$ in $k$ variables.

Lean: `New.mul_sum_exponentOf` (New/UpperBound/ElementaryDivisors/Depth.lean).

*Proof.* Swapping two indices permutes the exponents, so the sum does not depend on the index $b$ of $x$. Summing over $b$ gives $n$ for each exponent. $\square$

**Lemma.** For $0 < r$ and $2r \le k$, the costs $c(x) = \epsilon_r(x)/P^{2r}$ (for $b \ge 2r$) or $\epsilon_r(x)/P$ (for $b < 2r$) satisfy $\sum_x c(x) \le N(k/P^{2r} + r^2/P)$.

Lean: `New.FrobeniusCycle.sum_deepIndicator_div_le` (New/UpperBound/ElementaryDivisors/Depth.lean).

*Proof.* Each index is deep in $N/2$ letters. At most $k$ indices have $b \ge 2r$, and $2r$ have $b < 2r$. So the sum is at most $k(N/2)/P^{2r} + 2r(N/2)/P \le Nk/P^{2r} + Nr^2/P$, using $r \le r^2$. $\square$

**Theorem (Few deep forms).** Let $K$ have characteristic $p$, $0 < r$ and $2r \le k$. For every $M$,

$$\sum_{d < M}\dim\mathrm{deepForms}(k, n, r, d+1) \le c_{\mathrm{div}}\,|\mathrm{Mon}(k, n)|^N.$$

Lean: `New.FrobeniusCycle.sum_finrank_deepForms_le` (New/UpperBound/ElementaryDivisors/Depth.lean).

*Proof.* Let $\mathrm{cost}(\beta) = \sum_x\beta(x)c(x)$. By the theorem on costly monomials and the restriction lemma, $\dim\mathrm{deepForms}(d+1) \le \#\{\beta : d < \lfloor\mathrm{cost}(\beta)\rfloor\}$. Summing over $d < M$, each $\beta$ is counted at most $\lfloor\mathrm{cost}(\beta)\rfloor \le \mathrm{cost}(\beta)$ times. With $|\mathrm{Exp}| = |\mathrm{Mon}(k,n)|^N$ and the two lemmas,

$$\sum_\beta\mathrm{cost}(\beta) = \sum_x c(x)\sum_\beta\beta(x) = \frac{|\mathrm{Exp}|\,n}{k}\sum_x c(x) \le |\mathrm{Exp}|\,Nn\Big(\frac{1}{P^{2r}} + \frac{r^2}{kP}\Big). \qquad\square$$

In the model case $k = 2$, $r = 1$ only $b < 2r$ occurs, and $c_{\mathrm{div}} = Nn/P^2 + Nn/(2P)$. A monomial of degree $n$ in each letter has mean depth $Nn/2$, so the mean cost $Nn/(2P)$ is the depth divided by $P$.

### The colength of the origin functions

**Theorem.** Assume the size conditions and that $p$ is not a unit of $O$. Let every edge occur. There are $Q$, $R$, $d$ with: the image of $Q$ is $\mathrm{originFunctions}$; $RQ = 1$; $Qd = \mathrm{edgeRestriction}$; and

$$\det d \;\Big|\; w^{\,|X|\,\lfloor c_{\mathrm{div}}|\mathrm{Exp}|\rfloor}.$$

Lean: `New.FrobeniusCycle.IsLargeDegree.exists_basis_det_dvd` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

*Proof.* As $p$ is not a unit, the residue field of $O$ has characteristic $p$ (`New.FrobeniusCycle.charP_residueField`). The set $\mathrm{Exp}$ is finite, so all depths are at most some $x$. The theorem of Section 3 gives $Q$, $R$, $d$ with $\det d \mid w^{|X|\sum_{\delta<x}\dim\mathrm{deepForms}(\delta+1)}$, and the theorem on few deep forms, for the reduced Frobenius cycle (which has the same $P$, so the same $c_{\mathrm{div}}$), bounds the sum by $\lfloor c_{\mathrm{div}}|\mathrm{Exp}|\rfloor$. The image of $Q$ lies in the origin functions, and every origin function $\psi$ equals $Q(R\psi)$ by the last lemma of Section 3. $\square$

**Remark (Formalization).** The depth bound $x$ is taken by `Finite.exists_le`, and $Q$, $R$, $d$ come from existence statements. Nothing later depends on these choices: only $RQ = 1$, $Qd = \mathrm{edgeRestriction}$, the image of $Q$ and the bound on $\det d$ are used. The bound is a power of $w$, not of $p$. Two such ends give $w^{2|X|c_{\mathrm{div}}|\mathrm{Exp}|} = p^{|X|c_{\mathrm{div}}|\mathrm{Exp}|}$ in Section 8.
