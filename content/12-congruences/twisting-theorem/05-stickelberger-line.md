---
title: Stickelberger systems on a line
lean:
  - New/Congruences/Selmer/StickelbergerLine.lean
decls:
  - New.Selmer.isFromU1_pointChar
  - New.Selmer.coe_eval_groupRingEval_universalChar
  - New.Selmer.ellVal_one_sub_mul_one_sub_inv_le
  - New.Selmer.ellVal_eulerFactor_le
  - New.Selmer.exists_polynomial_eulerFactor
  - New.Selmer.one_add_X_pow_sub_one_dvd
  - New.Selmer.le_ellVal_one_add_pow_sub_one
  - New.Selmer.exists_ellVal_eval_le_gaussVal
  - New.Selmer.lineChar
  - New.Selmer.eval_single_groupRingEval_universalChar
  - New.Selmer.StickelbergerSystem.eventually_le_ellVal_sub
  - New.Selmer.StickelbergerSystem.groupRingEval_element_eq_mul_prod_eulerFactor
  - New.Selmer.StickelbergerSystem.exists_congruence_lineChar_element
  - New.Selmer.StickelbergerSystem.ellVal_one_element_singleton_le
  - New.Selmer.StickelbergerSystem.exists_point_ellVal_universalChar_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Stickelberger systems on a line

Let $J$ be a set of tied auxiliary primes with first prime $P_0$, and $\psi_X = \prod_j (1 + X_j)^{h_j}$ the polynomial character. The value $P = \psi_X(\Theta_J)$ is a polynomial in the variables $X_j$. This section finds a point $y$ with $v(y_j) \geq \rho$ at which $v(P(y))$ is at most $\beta + s_0\rho$. The point lies on the line on which all variables but the one of $P_0$ vanish. All results are in [StickelbergerLine.lean](lean:New/Congruences/Selmer/StickelbergerLine.lean#L1).

Background used: tied primes `New.Selmer.IsTiedPrimes` and the character $\prod_j \zeta_j^{h_j}$ `New.Selmer.pointChar` ([auxiliary primes](/chapter/tied-traces/#auxiliary-primes)); the polynomial character `New.Selmer.universalChar` with $\psi_X(g)$ at $X = \zeta - 1$ equal to the point character, `New.Selmer.aeval_sub_one_universalChar` ([one system for all twists](/chapter/tied-selmer-groups/#one-system-for-all-twists)); the Gauss valuation with $v_\rho(fg) = v_\rho(f) + v_\rho(g)$, $v_\rho(g) \leq v(g(0))$, $v_\rho(g) \leq \rho$ if the coefficient of $X$ is a unit, and a point $y$ with $v(y) \geq \rho$ and $v(g(y)) = v_\rho(g)$ ([the other tools](/chapter/fitting-ideals/#the-other-tools)).

Recall from [auxiliary primes](/chapter/tied-traces/#auxiliary-primes) what tied primes give: an auxiliary set $J$ with first prime $P_0 \in J$; for each $v \in J$ a place above $v$, a Frobenius element $\varphi_v$, a character $h_v \colon G \to \mathbb{Z}/\ell^N$ that is a character for $\{v\}$, and $\mathrm{N}v \equiv 1 \bmod \ell^N$; and for $v \neq P_0$, $h_{P_0}(\varphi_v) = 1$.

### Characters at roots of unity

**Lemma.** Let $\zeta_j^q = 1$. If each $h_j$ with $\zeta_j \neq 1$ is a character for $I$ with respect to $S$, then so is $g \mapsto \prod_j \zeta_j^{h_j(g)}$. For an element $a$ of the group ring of $\mathrm{Cl}_Q$ over $\bar{\mathbb{Z}}_\ell$, the value of $\psi_X(a)$ at $X = (\zeta_j - 1)_j$ is the value at $a$ of the character $\prod_j \zeta_j^{h_j}$.

Lean: `New.Selmer.isFromU1_pointChar`, `New.Selmer.coe_eval_groupRingEval_universalChar` (New/Congruences/Selmer/StickelbergerLine.lean).

*Proof.* The character is the product over $j$ of $\zeta_j^{h_j}$, the image of $h_j$ under a homomorphism. A factor with $\zeta_j = 1$ is trivial. The lemma of section 2 on products, images and the trivial character gives the first claim. For the second, evaluation at $\zeta - 1$ is a linear map, it commutes with the evaluation on the group ring, and it sends $\psi_X(g)$ to the point character at $g$. $\square$

### Valuations of Euler factors

**Lemma.** Let $a$, $b$ and $q$ be units with $v(a - b) \geq M$, $v(q - 1) \geq M$ and $v(b - 1) < M$. Then for every integer $k$,
$$v\bigl((1 - a q^k)(1 - a^{-1} q^k)\bigr) \leq 2v(b - 1).$$
If in addition $q$ is a natural number and $\mathrm{len}(\mathrm{exps}) \cdot 2v(b - 1) < M$, then $v(\mathrm{Eul}(a, q)) \leq \mathrm{len}(\mathrm{exps}) \cdot 2v(b - 1)$.

Lean: `New.Selmer.ellVal_one_sub_mul_one_sub_inv_le`, `New.Selmer.ellVal_eulerFactor_le` (New/Congruences/Selmer/StickelbergerLine.lean).

*Proof.* Since $a - 1$ divides $a^n - 1$, $v(q^k - 1) \geq v(q - 1) \geq M$; for $k < 0$ use $v(x^{-1} - y^{-1}) = v(x - y)$ for units. Then $a q^k - 1 - (b - 1) = a(q^k - 1) + (a - b)$ has valuation at least $M > v(b - 1)$, so $v(1 - a q^k) = v(b - 1)$ by the ultrametric inequality. In the same way $v(1 - a^{-1}q^k) = v(b^{-1} - 1) = v(b - 1)$. Add the two. For the Euler factor use induction on the list: each new pair gives at most $2v(b - 1)$, and the condition on $M$ holds for the shorter list. $\square$

### Polynomials for Euler factors

**Lemma.** Let $\alpha$ and $q$ be units and $r = \mathrm{len}(\mathrm{exps})$. There is $R \in \bar{\mathbb{Z}}_\ell[X]$ with $v_\rho(R) \leq 2r\rho$ and, for every integral $\zeta \neq 0$,
$$R(\zeta - 1) = \zeta^r \, \mathrm{Eul}(\alpha\zeta, q).$$

Lean: `New.Selmer.exists_polynomial_eulerFactor` (New/Congruences/Selmer/StickelbergerLine.lean).

*Proof.* Induction on the list. For $e$ and $c = q^{-e}$ take $S = (1 - \alpha c(1 + X))(1 + X - \alpha^{-1}c)$. At $X = \zeta - 1$ it is $(1 - \alpha c\zeta)(\zeta - \alpha^{-1}c) = \zeta(1 - \alpha\zeta c)(1 - (\alpha\zeta)^{-1}c)$. Each factor has a unit as coefficient of $X$, so it has Gauss valuation at most $\rho$, and $v_\rho(S) \leq 2\rho$. Multiply $S$ by the polynomial for the rest of the list. $\square$

### A congruence gives a point

**Lemma.** Let $q \geq 1$.

1. If $D \in \bar{\mathbb{Z}}_\ell[X]$ vanishes at $\zeta - 1$ for every $\zeta$ with $\zeta^q = 1$, then $(1 + X)^q - 1$ divides $D$.
2. If $\rho \leq 1$ and $v(y) \geq \rho$, then $v((1 + y)^{\ell^N} - 1) \geq N\rho$.
3. Let $\rho \leq 1$, let $(1 + X)^{\ell^N} - 1$ divide $(1 + X)^j P - R$, and let $v_\rho(R) < N\rho$. Then there is $y$ with $v(y) \geq \rho$ and $v(P(y)) \leq v_\rho(R)$.

Lean: `New.Selmer.one_add_X_pow_sub_one_dvd`, `New.Selmer.le_ellVal_one_add_pow_sub_one`, `New.Selmer.exists_ellVal_eval_le_gaussVal` (New/Congruences/Selmer/StickelbergerLine.lean).

*Proof.* (1) Let $\zeta$ be a primitive $q$-th root of unity. The values $\zeta^i - 1$, $i < q$, are $q$ distinct roots of the remainder of $D$ modulo the monic polynomial $(1 + X)^q - 1$ of degree $q$. The remainder has degree less than $q$, so it is $0$.

(2) $(1 + y)^{\ell^N} - 1 = y \cdot \sum_{i < \ell^N}(1 + y)^i$, and the geometric sum lemma gives the bound $N\rho$ for the sum with $v((1 + y) - 1) \geq \rho$.

(3) Choose $y$ with $v(y) \geq \rho$ and $v(R(y)) = v_\rho(R)$. Then $(1 + y)^{\ell^N} - 1$ divides $(1 + y)^j P(y) - R(y)$, so by (2) this difference has valuation at least $N\rho > v(R(y))$. So $v((1 + y)^j P(y)) = v(R(y))$, and $v(P(y)) \leq v((1 + y)^j P(y))$. $\square$

### The line

**Definition.** For a character $h \colon G \to \mathbb{Z}/q$, put $\mathrm{line}_h(g) = (1 + X)^{h(g)}$, with $h(g)$ read as a natural number less than $q$.

Lean: `New.Selmer.lineChar` (New/Congruences/Selmer/StickelbergerLine.lean).

**Lemma.** The value of $\psi_X(a)$ at the point with $j$-th coordinate $y$ and all others $0$ is $\mathrm{line}_{h_j}(a)$ at $X = y$. At $X = \zeta - 1$ with $\zeta^q = 1$, $\mathrm{line}_h(a)$ is the value of $\zeta^h$ at $a$, and at $X = 0$ it is $1(a)$.

Lean: `New.Selmer.eval_single_groupRingEval_universalChar`, `New.Selmer.coe_eval_groupRingEval_lineChar`, `New.Selmer.coe_eval_zero_groupRingEval_lineChar` (New/Congruences/Selmer/StickelbergerLine.lean).

*Proof.* At that point the factors $(1 + X_i)^{h_i}$ with $i \neq j$ are $1$. Evaluation is linear and commutes with the group ring evaluation. $\square$

### The system on the line

Fix a Stickelberger system $Y$ with character $\vartheta$, $r$ exponents and number $\beta$.

**Lemma.** For each $M$, every $g$ near $g_0$ has $v(\vartheta(g) - \vartheta(g_0)) \geq M$.

Lean: `New.Selmer.StickelbergerSystem.eventually_le_ellVal_sub` (New/Congruences/Selmer/StickelbergerLine.lean).

*Proof.* $\vartheta$ is continuous, so $\vartheta(g)$ is in the closed ball of radius $\|\ell^M\|$ about $\vartheta(g_0)$ for $g$ near $g_0$. $\square$

**Lemma.** Let $J$ be tied with first prime $P_0$, and $\zeta^{\ell^N} = 1$. Then
$$\zeta^{h_{P_0}}(\Theta_J) = \zeta^{h_{P_0}}(\Theta_{\{P_0\}}) \prod_{v \in J \setminus \{P_0\}} \mathrm{Eul}(\vartheta(\varphi_v)\zeta, \mathrm{N}v).$$

Lean: `New.Selmer.StickelbergerSystem.groupRingEval_element_eq_mul_prod_eulerFactor` (New/Congruences/Selmer/StickelbergerLine.lean).

*Proof.* The character $\psi = \zeta^{h_{P_0}}$ is a character for $\{P_0\}$. For $v \neq P_0$ in $J$, $h_{P_0}(\varphi_v) = 1$, so $\psi(\varphi_v) = \zeta$. Apply the norm relation for several primes with $Q = \{P_0\}$ and $I = J \setminus \{P_0\}$. $\square$

**Lemma.** Let $N \neq 0$ and $\rho \geq 0$. There is $R$ with $v_\rho(R) \leq \#(J \setminus \{P_0\}) \cdot 2r\rho$ such that $(1 + X)^{\ell^N} - 1$ divides
$$(1 + X)^{r \cdot \#(J \setminus \{P_0\})}\, \mathrm{line}_{h_{P_0}}(\Theta_J) - \mathrm{line}_{h_{P_0}}(\Theta_{\{P_0\}}) \cdot R.$$

Lean: `New.Selmer.StickelbergerSystem.exists_congruence_lineChar_element` (New/Congruences/Selmer/StickelbergerLine.lean).

*Proof.* For $v \neq P_0$ the norm $\mathrm{N}v \equiv 1 \bmod \ell^N$ is a unit. The lemma on polynomials gives $R_v$ with $v_\rho(R_v) \leq 2r\rho$ and $R_v(\zeta - 1) = \zeta^r \mathrm{Eul}(\vartheta(\varphi_v)\zeta, \mathrm{N}v)$. Put $R = \prod_v R_v$; the Gauss valuation adds. By (1) of the congruence lemma it is enough to check that the difference vanishes at $\zeta - 1$ for every $\zeta$ with $\zeta^{\ell^N} = 1$. There the two line values are $\zeta^{h_{P_0}}(\Theta_J)$ and $\zeta^{h_{P_0}}(\Theta_{\{P_0\}})$, and $R(\zeta - 1) = \zeta^{r\#(J \setminus \{P_0\})}\prod_v \mathrm{Eul}$. The last lemma gives the identity. $\square$

**Lemma.** Let $\beta < M \leq N$ and $v(\vartheta(\varphi_{P_0}) - \vartheta(g_0)) \geq M$. Then $v(1(\Theta_{\{P_0\}})) \leq \beta$.

Lean: `New.Selmer.StickelbergerSystem.ellVal_one_element_singleton_le` (New/Congruences/Selmer/StickelbergerLine.lean).

*Proof.* The norm relation with $Q = \emptyset$, $P = P_0$ and the trivial character gives $1(\Theta_{\{P_0\}}) = 1(\Theta_\emptyset)\, \mathrm{Eul}(\vartheta(\varphi_{P_0}), \mathrm{N}P_0)$. Since $\mathrm{N}P_0 \equiv 1 \bmod \ell^N$, $v(\mathrm{N}P_0 - 1) \geq N \geq M$. The second part of the lemma on Euler factors, with $a = \vartheta(\varphi_{P_0})$ and $b = \vartheta(g_0)$, bounds the factor by $r \cdot 2v(\vartheta(g_0) - 1)$; its condition holds since $r \cdot 2v(\vartheta(g_0) - 1) \leq \beta < M$. Add $v(1(\Theta_\emptyset))$. $\square$

**Theorem.** Let $J$ be tied with first prime $P_0$, and let $M$, $s_0 \geq 1$ and $\rho \geq 0$ satisfy
$$\beta + 1 < M \leq N\rho, \qquad v(\vartheta(\varphi_{P_0}) - \vartheta(g_0)) \geq M, \qquad 2r\#J \leq s_0, \qquad s_0\rho < 1.$$
Then there is a point $y = (y_j)_{j \in J}$ with $v(y_j) \geq \rho$ for all $j$ and
$$v\bigl(\psi_X(\Theta_J)(y)\bigr) \leq \beta + s_0\rho.$$

Lean: `New.Selmer.StickelbergerSystem.exists_point_ellVal_universalChar_le` (New/Congruences/Selmer/StickelbergerLine.lean).

*Proof.* From $s_0 \geq 1$ and $s_0\rho < 1$, $\rho \leq 1$, so $M \leq N\rho \leq N$, and $N \neq 0$. Let $R_0 = \mathrm{line}_{h_{P_0}}(\Theta_{\{P_0\}})$ and take $R_1$ from the congruence lemma. Then $v_\rho(R_0) \leq v(R_0(0)) = v(1(\Theta_{\{P_0\}})) \leq \beta$ by the last lemma. Also $v_\rho(R_1) \leq \#(J \setminus \{P_0\}) \cdot 2r\rho \leq s_0\rho$. So
$$v_\rho(R_0R_1) \leq \beta + s_0\rho \leq \beta + 1 < M \leq N\rho.$$
Part (3) of the congruence lemma gives $y$ with $v(y) \geq \rho$ and $v(\mathrm{line}_{h_{P_0}}(\Theta_J)(y)) \leq v_\rho(R_0R_1)$. Take the point with coordinate $y$ at $P_0$ and $0$ elsewhere. The coordinates $0$ have valuation $\infty \geq \rho$, and the value of $\psi_X(\Theta_J)$ there is the line value at $y$. $\square$

The two conditions on the Frobenius element of $P_0$ and on $N$ are met by the choice of the tied primes. The first prime $P_0$ has its Frobenius element in an open set $W$ near $g_0$, and the lemma on continuity above makes $W$ small enough. Section 8 makes these choices.
