---
title: One principal minor
lean:
  - New/Appendix/DiscreteSeries/MinorSecondOrder.lean
  - New/Appendix/DiscreteSeries/OneMinor.lean
decls:
  - New.DiscreteSeries.crossTrace
  - New.DiscreteSeries.crossTraceSum
  - New.DiscreteSeries.exists_expMinor_eq_cexp
  - New.DiscreteSeries.norm_le_mul_sq_of_even
  - New.DiscreteSeries.logMinorRemainder_scaleCross_neg
  - New.DiscreteSeries.exists_det_one_add_proj_mul_eq_exp
  - New.DiscreteSeries.norm_principalMinor_sq_le_exp
  - New.DiscreteSeries.reducedExp
  - New.DiscreteSeries.det_reducedExp
  - New.DiscreteSeries.flenstedJensen_reducedExp
  - New.DiscreteSeries.crossTraceSum_coordProj_eq
  - New.DiscreteSeries.exists_principalMinor_conj_reducedExp_eq_cexp
status: drafted
drafted_by: writer@claude-opus-5-5
---
## One principal minor

On $K$ the coefficient $c_l$ is a product of powers of principal minors. Near the identity of $U(\varepsilon)$ the integral of Flensted-Jensen is an average of such products. So the Gaussian shape of section 5 rests on two facts about one principal minor: a bound for its size on a unitary matrix, and a second order expansion near $1$ with an error that is small in a precise sense.

In this section all norms are Frobenius norms. For a set $S$ of indices, $P$ is the diagonal projection to the coordinates in $S$, and $\det_S A$ is the principal minor of $A$ on $S$. The commutator $[P, A] = PA - AP$ consists of the two blocks of $A$ that cross $S$: the entries $(i, j)$ with exactly one of $i, j$ in $S$. No constant in this section depends on the dimension.

### The size of a minor of a unitary matrix

**Theorem (Size of one minor).** Let $k$ be unitary and let $S$ be a set of indices. Then
$$ |\det\nolimits_S k|^2 \leq \exp\left(-\tfrac12 \|[P, k]\|^2\right). $$
Lean: `New.DiscreteSeries.norm_principalMinor_sq_le_exp` (New/Appendix/DiscreteSeries/OneMinor.lean).

*Proof.* Put $Y = (1 - P) + PkP$ and $M = (1 - P)kP$. Then $\det_S k = \det Y$. The cross terms of $Y^*Y$ vanish, since $(1-P)P = 0$. So
$$ Y^* Y = (1 - P) + P k^* P k P = 1 - M^* M, $$
where the second equality uses $P = P k^* k P = P k^* P k P + P k^* (1-P) k P$. For every matrix $Y$, the eigenvalues $t_i \geq 0$ of $Y^* Y$ give $|\det Y|^2 = \prod t_i \leq \prod e^{t_i - 1} = \exp\operatorname{tr}(Y^*Y - 1)$. Here $\operatorname{tr}(Y^* Y - 1) = -\|M\|^2$. Finally $[P, k] = Pk(1-P) - (1-P)kP$, and for unitary $k$ the two blocks have the same norm, so $\|[P,k]\|^2 = 2\|M\|^2$. $\square$

So a minor of a unitary matrix is small when the matrix has large crossing blocks. In section 5 this bounds $c_l$ on $K$ by a Gaussian in a weighted sum of the entries.

### Three exponentials, to second order

Let $Q$ be an orthogonal projection. For square matrices $A$ and $B$ the *crossing trace* is $\operatorname{tr}(QA(1-Q)B)$.
Lean: `New.DiscreteSeries.crossTrace` (New/Appendix/DiscreteSeries/MinorSecondOrder.lean).

For three matrices $A_1, A_2, A_3$ the *crossing sum* is
$$ \chi_Q(A_1, A_2, A_3) = \frac12\sum_{i} \operatorname{tr}(QA_i(1-Q)A_i) + \sum_{i < j}\operatorname{tr}(QA_i(1-Q)A_j). $$
Lean: `New.DiscreteSeries.crossTraceSum` (New/Appendix/DiscreteSeries/MinorSecondOrder.lean).

The crossing sum is the second order term of $\log\det(1 + Q(e^{A_1}e^{A_2}e^{A_3} - 1))$. To see this, write $E = e^{A_1}e^{A_2}e^{A_3} - 1 = L + S + O(\delta^3)$, with $L = \sum A_i$ and $S = \frac12\sum A_i^2 + \sum_{i<j}A_iA_j$. Then $\log\det(1 + QE) = \operatorname{tr}(QE) - \frac12\operatorname{tr}(QEQE) + O(\delta^3)$. The terms of second order are $\operatorname{tr}(QS) - \frac12 \operatorname{tr}(QLQL)$, and $\operatorname{tr}(QA_iA_j) - \operatorname{tr}(QA_iQA_j)$ is the crossing trace.

**Lemma (Third order).** Let $\|A_i\| \leq \rho \leq 1/10$. Then
$$ \det(1 + Q(e^{A_1}e^{A_2}e^{A_3} - 1)) = \exp\big(\operatorname{tr}Q(A_1 + A_2 + A_3) + \chi_Q(A_1, A_2, A_3) + r\big), \qquad |r| \leq 216\rho^3. $$
Lean: `New.DiscreteSeries.exists_expMinor_eq_cexp` (New/Appendix/DiscreteSeries/MinorSecondOrder.lean).

*Proof.* Expand each exponential to second order with a remainder $A R$, $\|R\| \leq \|A\|^2$, and multiply. Write $\log(1+M) = \int_0^1 (1 + sM)^{-1} M\, ds$ for $\|M\| \leq 1/2$ and expand the integrand to first order. All the remainders are bounded by geometric series, and the constants add up to $216$. $\square$

The bound $216\rho^3$ is not good enough for Laplace's method. We need a bound that is quadratic in the crossing parts. If all $A_i$ commute with $Q$, then $\det(1 + Q(e^{A_1}e^{A_2}e^{A_3} - 1)) = \exp\operatorname{tr}Q(A_1 + A_2 + A_3)$ exactly, and the crossing sum is $0$. So the remainder vanishes when the crossing parts vanish. The next two lemmas turn this into a quantitative bound.

**Lemma (Schwarz's lemma for even functions).** Let $f$ be holomorphic on the disc $|z| < R$, even, with $f(0) = 0$ and $|f| \leq C$ there. Then $|f(z)| \leq C(|z|/R)^2$ for $|z| < R$.
Lean: `New.DiscreteSeries.norm_le_mul_sq_of_even` (New/Appendix/DiscreteSeries/MinorSecondOrder.lean).

*Proof.* Since $f$ is even, $f'(0) = 0$. So $f(z)/z^2$ is holomorphic, and the maximum principle gives the bound, as in the proof of Schwarz's lemma (Rudin, *Real and Complex Analysis*, Theorem 12.2). $\square$

For $\tau \in \mathbb{C}$ let $A_i(\tau)$ be $A_i$ with its crossing part $QA_i(1-Q) + (1-Q)A_iQ$ multiplied by $\tau$. Let $f(\tau)$ be the principal logarithm of the quotient of the minor at $A_i(\tau)$ by $\exp$ of its terms of first and second order.

**Lemma (Evenness).** The function $f$ is even.
Lean: `New.DiscreteSeries.logMinorRemainder_scaleCross_neg` (New/Appendix/DiscreteSeries/MinorSecondOrder.lean).

*Proof.* Let $U = 2Q - 1$. Then $U^2 = 1$ and $U$ commutes with $Q$. Conjugation by $U$ keeps the parts of a matrix that commute with $Q$ and changes the sign of the crossing part. So $U A_i(\tau) U = A_i(-\tau)$. The minor and the first and second order terms are invariant under conjugation by $U$. $\square$

**Theorem (One minor to second order).** Let $Q$ be an orthogonal projection and $\delta \leq 1/20$. Let $\|A_i\| \leq \delta$ and $\|[Q, A_i]\| \leq \zeta$ for $i = 1, 2, 3$. Then
$$ \det(1 + Q(e^{A_1}e^{A_2}e^{A_3} - 1)) = \exp\big(\operatorname{tr}Q(A_1 + A_2 + A_3) + \chi_Q(A_1, A_2, A_3) + r\big), \qquad |r| \leq 10^4\delta\zeta^2. $$
Lean: `New.DiscreteSeries.exists_det_one_add_proj_mul_eq_exp` (New/Appendix/DiscreteSeries/MinorSecondOrder.lean).

*Proof.* There are three cases. If $\delta \leq \zeta$, the third order lemma gives $|r| \leq 216\delta^3 \leq 10^4\delta\zeta^2$. If $\zeta = 0$, all $A_i$ commute with $Q$ and $r = 0$. Let $0 < \zeta < \delta$. For $|\tau| < \delta/\zeta$ we have $\|A_i(\tau)\| \leq \delta + |\tau|\zeta \leq 2\delta \leq 1/10$, so the third order lemma gives $|f(\tau)| \leq 216(2\delta)^3$. The function $f$ is holomorphic, even, and $f(0) = 0$. Schwarz's lemma with $R = \delta/\zeta > 1$ gives
$$ |r| = |f(1)| \leq 216(2\delta)^3(\zeta/\delta)^2 = 1728\,\delta\zeta^2. \qquad \square $$

**Remark (Formalization).** The source proves that $f$ is holomorphic on the disc by showing that the quotient stays in the slit plane, where the principal logarithm is holomorphic. The remainder $r$ is defined as this principal logarithm, so it is a specific number, not one chosen by `choose`.

### The reduced exponential

Near $1$ an element of $U(\varepsilon)$ is $e^Z$ with $Z$ in the Lie algebra, that is $Z^* J_\varepsilon + J_\varepsilon Z = 0$. Let $o \in \mathbb{Z}^n$ order the indices. Let $u$ keep the entries $Z_{ij}$ with $\varepsilon_i = \varepsilon_j$ and $o_i < o_j$, and let $v$ keep those with $\varepsilon_i = \varepsilon_j$ and $o_j < o_i$. The *reduced exponential* is
$$ \hat g = e^{-u} e^{Z} e^{-v}. $$
Lean: `New.DiscreteSeries.reducedExp` (New/Appendix/DiscreteSeries/OneMinor.lean).

**Lemma (Determinant of the reduced exponential).** $\det\hat g = e^{\operatorname{tr}Z}$.
Lean: `New.DiscreteSeries.det_reducedExp` (New/Appendix/DiscreteSeries/OneMinor.lean).

*Proof.* The matrices $u$ and $v$ have zero diagonal, so $\det e^{-u} = \det e^{-v} = 1$. $\square$

**Lemma (Triangular factors).** Let $l$ have a gap and $\|Z\| \leq 1/20$. Then the integral of Flensted-Jensen with first argument $1$ takes the same value at $\hat g$ for the order $o = l$ and at $e^Z$.
Lean: `New.DiscreteSeries.flenstedJensen_reducedExp` (New/Appendix/DiscreteSeries/OneMinor.lean).

*Proof.* The factors $e^{-u}$ and $e^{-v}$ are block diagonal and triangular, with diagonal $1$. The previous chapter shows that triangular factors on the two sides multiply the integral by a character of their diagonals, if the matrices involved are accretive. Here the character is $1$, and all matrices are within $1/10$ of $1$, so they are accretive. $\square$

The point of the reduced exponential is that its crossing sum is explicit.

**Lemma (Crossing sum at a coordinate projection).** Let $Z$ be in the Lie algebra of $U(\varepsilon)$, let $P$ be the projection to $S$, and assume $o_i < o_j$ for $i \in S$, $j \notin S$. Then
$$ \chi_P(-u, Z, -v) = \tfrac14\|[P, Z]\|^2. $$
Lean: `New.DiscreteSeries.crossTraceSum_coordProj_eq` (New/Appendix/DiscreteSeries/OneMinor.lean).

*Proof.* By the Lie algebra condition, $Z_{ij} = -\overline{Z_{ji}}$ when $\varepsilon_i = \varepsilon_j$, and $Z_{ij} = \overline{Z_{ji}}$ when $\varepsilon_i \neq \varepsilon_j$. Let $C$ and $N$ be the sums of $|Z_{ji}|^2$ over $i \in S$, $j \notin S$, with equal and with opposite signs. Then $\|[P, Z]\|^2 = 2(C + N)$. Each crossing trace is a sum of $A_{ij}B_{ji}$ over $i \in S$, $j \notin S$. Since $o_i < o_j$ there, $u$ keeps the entry $(i, j)$ with equal signs and $v$ keeps the entry $(j, i)$. One finds that the traces for $(-u,-u)$ and $(-v,-v)$ are $0$, for $(Z, Z)$ it is $N - C$, for $(-u, Z)$ and $(Z, -v)$ it is $C$, and for $(-u, -v)$ it is $-C$. So
$$ \chi_P = \tfrac12(N - C) + C + C - C = \tfrac12(C + N) = \tfrac14\|[P,Z]\|^2. \qquad \square $$

So for the reduced exponential the second order term is real and nonnegative. This is the source of the positive Gaussian $\varrho$ of section 5.

### A minor of a conjugated reduced exponential

**Theorem (Minor of a conjugate).** Let $o$ be injective, with $o_i < o_j$ for $i \in S$ and $j \notin S$. Let $Z$ be in the Lie algebra of $U(\varepsilon)$ with $\|Z\| \leq \delta \leq 1/20$. Let $k$ be unitary and block diagonal. Then
$$ \det\nolimits_S(k^* \hat g k) = \exp\left(\operatorname{tr}(PZ) + \tfrac14\|[P, Z]\|^2 + r\right), \qquad |r| \leq 10^5\delta\left(\|[P, Z]\|^2 + \|[P, k]\|^2\right). $$
Lean: `New.DiscreteSeries.exists_principalMinor_conj_reducedExp_eq_cexp` (New/Appendix/DiscreteSeries/OneMinor.lean).

*Proof.* Let $Q = kPk^*$, an orthogonal projection. Then $\det_S(k^*\hat g k) = \det(1 + Q(\hat g - 1))$. Put $x = \|[P,Z]\|$, $\kappa = \|[P,k]\|$ and $\zeta = x + 2\delta\kappa$. We have $\|Q - P\| = \kappa$, so $\|[Q, A]\| \leq \|[P, A]\| + 2\|A\|\kappa$. The masks $u$ and $v$ have commutators with $P$ of norm at most $x$, so all three exponents have commutator with $Q$ at most $\zeta$. The theorem on one minor gives the expansion with $Q$ and an error $10^4\delta\zeta^2$. Now replace $Q$ by $P$ in the two main terms. The first order term changes by at most $\delta\kappa^2$; here one uses that $o$ is injective and $k$ is block diagonal. The crossing sum changes by at most $18\delta\kappa\zeta$. At $P$ the crossing sum is $x^2/4$ by the previous lemma. Finally $\delta\kappa^2 + 18\delta\kappa\zeta + 10^4\delta\zeta^2 \leq 10^5\delta(x^2 + \kappa^2)$, since $\zeta \leq x + \kappa$. $\square$

**Remark (Formalization).** The source states this theorem with the finite sums sealed, so that the checker does not unfold them during definitional checks. This changes nothing in the statement.
