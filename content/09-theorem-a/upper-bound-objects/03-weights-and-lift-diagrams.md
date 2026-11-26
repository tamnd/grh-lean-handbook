---
title: Weights and lift diagrams
lean:
  - New/UpperBound/Objects/Weights.lean
decls:
  - New.Data.columnCount
  - New.Data.lastEntry
  - New.twiceBlockEntry
  - New.Data.paramX
  - New.Data.weightX
  - New.Data.liftDiagram
  - New.Data.weightX_succ
  - New.Data.liftDiagram_zero
  - New.Data.liftDiagram_succ
  - New.Data.liftDiagram_eq_sum_columnCount
  - New.Data.liftDiagram_le
  - New.Data.weightX_eq
  - New.Data.lastEntry_eq
  - New.Data.keptColumns
  - New.Data.columnsY
  - New.Data.weightY
  - New.Data.weightY_eq_weightX_add
  - New.Data.keptColumns_le_columnCount
  - New.Data.weightY_eq
  - New.Data.columnsY_le
  - New.Data.branchExponent
  - New.Data.branchExponent_eq
  - New.Data.sum_branchExponent
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Weights and lift diagrams

The forms on the definite spaces $X_j$ and $Y_m$ take values in irreducible representations of compact unitary groups. Such a representation is fixed by its highest weight at each infinite place $\tau$: a nonincreasing sequence of integers $\mu_0 \ge \mu_1 \ge \dots \ge \mu_{n-1}$. This section fixes these weights. The two maps of the proof must land in the same space of forms on $Y_m$, so the weight that the composite lift gives on $Y_m$ must be a weight that branching from $X_m$ allows. That is the interlacing at the end of the section.

### Weights by their columns

A nonincreasing sequence $\mu$ of length $n$ is fixed by its last entry $\mu_{n-1}$ and by the numbers of columns of each height of the Young diagram of $\mu - \mu_{n-1}$. A column of height $h$, with $1 \le h < n$, adds $1$ to the entries $\mu_0, \dots, \mu_{h-1}$. So
$$\mu_p = \mu_{n-1} + \sum_{p < h < n} c(h), \qquad c(h) = \mu_{h-1} - \mu_h.$$
The source fixes one table of column counts $c(h)$, common to all the $X_j$, and one last entry for each $j$. The rank $n_j$ decides which heights take part.

Recall that $a_\tau$ is $a$ at the $a$-places and $0$ elsewhere (`New.Data.firstRowExcess`), and that the lift weights are $\kappa_j(\tau) = \kappa(\tau) + (2j+1)\Delta/2$ ([liftWeight](/decl/New.Data.liftWeight/)), so $\kappa_{j+1} = \kappa_j + \Delta$.

**Definition (Column counts and last entries).** At the infinite place $\tau$, the number of columns of height $h$ is
$$c_\tau(h) = \begin{cases} a_\tau & h = 1,\\ \kappa_1(\tau) - \lfloor (k + t + 1)/2 \rfloor & h = k,\\ \Delta - (t+1) & h > k,\ t + 1 \mid h - k,\\ 0 & \text{otherwise.}\end{cases}$$
The last entry of the weight on $X_j$ is $\ell_0 = 0$ and $\ell_j = n_{j-1}/2 - \kappa_j(\tau)$ for $j \ge 1$.

Lean: `New.Data.columnCount` (New/UpperBound/Objects/Weights.lean).

Lean: `New.Data.lastEntry` (New/UpperBound/Objects/Weights.lean).

The case $h = 1$ is tested first, but $k > 1$, so the cases do not overlap. The subtraction in the case $h = k$ is in $\mathbb{N}$; it does not truncate, as $k + t + 1 \le \Delta/2 \le \kappa_1$.

So the heights in use are $1$, $k$ and $n_1, n_2, \dots$, since $n_i - k = i(t+1)$.

### Parameters and weights of the upper chain

The source defines the weights through doubled Harish-Chandra parameters, as the theta correspondence of discrete series acts on parameters. For a rank $n$, write $[n]$ for the block $((n-1)/2, (n-3)/2, \dots, (1-n)/2)$. Its doubled entries are $2[n]_p = n - 1 - 2p$ (`New.twiceBlockEntry`), and they sum to $0$.

**Definition (Parameters and weights of $X_j$).** The doubled parameter sequence at $\tau$ is
$$2\lambda_p = \begin{cases} 2[k]_p + 2a_\tau[p = 0] & p < k,\\ 2[t+1]_b - 2\kappa_{i+1}(\tau) & p = k + i(t+1) + b,\ b < t+1. \end{cases}$$
The parameter of $X_j$ is its first $n_j$ entries. The weight of $X_j$ is $\mu(X_j)_p = (2\lambda_p - 2[n_j]_p)/2$. The diagram of lift $j + 1$ is $\mu^+_{j+1,p} = \mu(X_j)_p + \kappa_{j+1}(\tau) - n_{j+1}/2$ for $p < n_j$, and $0$ for $p \ge n_j$.

Lean: `New.Data.paramX` (New/UpperBound/Objects/Weights.lean).

Lean: `New.Data.weightX` (New/UpperBound/Objects/Weights.lean).

Lean: `New.Data.liftDiagram` (New/UpperBound/Objects/Weights.lean).

The division by $2$ is exact, as $k$, $t + 1$ and $n_j$ are even (`New.Data.two_mul_weightX`). The lift diagram is the Young diagram that the theta lift of [theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/) uses for the step $X_j \to X_{j+1}$. The next lemma gives the rule for the step.

**Lemma (One lift).** For $p < n_{j+1}$, $\mu(X_{j+1})_p = \mu^+_{j+1,p} + n_j/2 - \kappa_{j+1}(\tau)$. For $p < k$, $\mu^+_{1,p} = a_\tau[p = 0] + \kappa_1(\tau) - n_1/2$. For $p < n_{j+1}$, $\mu^+_{j+2,p} = \mu^+_{j+1,p} + \Delta - (t+1)$.

Lean: `New.Data.weightX_succ` (New/UpperBound/Objects/Weights.lean).

Lean: `New.Data.liftDiagram_zero` (New/UpperBound/Objects/Weights.lean).

Lean: `New.Data.liftDiagram_succ` (New/UpperBound/Objects/Weights.lean).

*Proof.* For $p < n_j$, the first $n_j$ entries of $[n_{j+1}]$ are those of $[n_j]$ plus $(t+1)/2$, which gives the first formula there. For $p = n_j + b$ with $b < t + 1$, the entry of $[n_{j+1}]$ is $[t+1]_b - n_j/2$, and $2\lambda_p = 2[t+1]_b - 2\kappa_{j+1}$, so $\mu(X_{j+1})_p = n_j/2 - \kappa_{j+1}$, while $\mu^+_{j+1,p} = 0$. The second formula is the case $j = 0$, as $\mu(X_0)_p = a_\tau[p = 0]$ for $p < k$. The third follows from the first, from $\kappa_{j+2} = \kappa_{j+1} + \Delta$, and from $n_{j+2} = n_j + 2(t+1)$. $\square$

So the first lift creates $c_\tau(k)$ columns of height $k$ and $a_\tau$ boxes in the first row, and each later lift adds a block of $\Delta - (t+1)$ columns of full height. The column counts make this exact.

**Proposition (Columns of the diagrams and the weights).** For all $j$, $\tau$ and $p$:

1. $\mu^+_{j+1,p} = \sum_{p < u < n_{j+1}} c_\tau(u)$;
2. for $p < n_j$, $\mu(X_j)_p = \ell_j + \sum_{p < u < n_j} c_\tau(u)$;
3. $\ell_j = n_{j+1}/2 - \kappa_{j+1}(\tau) + c_\tau(n_j)$.

Lean: `New.Data.liftDiagram_eq_sum_columnCount` (New/UpperBound/Objects/Weights.lean).

Lean: `New.Data.weightX_eq` (New/UpperBound/Objects/Weights.lean).

Lean: `New.Data.lastEntry_eq` (New/UpperBound/Objects/Weights.lean).

*Proof.* For (1), induct on $j$. No column has a height strictly between $n_j$ and $n_{j+1}$, as $t + 1$ does not divide $u - k$ there. So the rows $p \ge n_j$ are $0$ on both sides. For $j = 0$ and $p < k$, the sum over $p < u < n_1$ picks up $c_\tau(1) = a_\tau$ if $p = 0$ and $c_\tau(k) = \kappa_1 - n_1/2$, which is the formula of the lemma. The step from $j$ to $j+1$ adds the single height $n_{j+1}$, with $c_\tau(n_{j+1}) = \Delta - (t+1)$, which is the recursion of the lemma. For (2), the case $j = 0$ is the definition, and the case $j + 1$ follows from (1) and the first formula of the lemma. For (3), compare (1) and (2) at the last row $p = n_j - 1$ of $\mu^+_{j+1}$. $\square$

The rows of the lift diagrams have explicit bounds. These bounds feed the archimedean estimates of [the archimedean size of the composite lift](/chapter/archimedean-size/).

**Lemma.** For $j < m$, row $p$ of $\mu^+_{j+1}$ at $\tau$ is at most $a_\tau + \kappa_{j+1}(\tau)$ if $p = 0$, at most $\kappa_{j+1}(\tau)$ if $0 < p < k$, and at most $m\Delta$ if $p \ge k$.

Lean: `New.Data.liftDiagram_le` (New/UpperBound/Objects/Weights.lean).

*Proof.* There are at most $\kappa_1$ columns of height $k$, and each later lift adds fewer than $\Delta$ columns. So row $p$ is at most $a_\tau[p = 0] + \kappa_1[p < k] + j\Delta$. As $\kappa_{j+1} = \kappa_1 + j\Delta$ and $j < m$, the three bounds follow. $\square$

### The weight of $Y_m$ and branching

The space $Y_m$ has rank $n_m - 1$. By the branching rule from $\mathrm{U}(n)$ to $\mathrm{U}(n-1)$ ([integral Weyl modules and branching](/chapter/weyl-modules/)), a representation of highest weight $\mu$ of $\mathrm{U}(X_m)$ contains the representation of highest weight $\mu'$ of $\mathrm{U}(Y_m)$ exactly when the two weights interlace: $\mu_p \ge \mu'_p \ge \mu_{p+1}$ for all $p < n_m - 1$. In the language of columns, branching removes one box from some columns. The source keeps a fixed number of columns at each height $h \equiv k \pmod{t+1}$ and shortens all the others by one box.

**Definition (The weight of $Y_m$).** The number of kept columns of height $h$ is $\Delta/2 - (t+1)/2$ if $h \ge k$ and $t + 1 \mid h - k$, and $0$ otherwise. The column count of $Y_m$ at height $h$ is
$$c'_\tau(h) = \mathrm{kept}(h) + \big(c_\tau(h+1) - \mathrm{kept}(h+1)\big).$$
The weight $\mu(Y_m)_p$ is $(2\lambda'_p - 2[n_m - 1]_p)/2$, where $2\lambda'$ is the decreasing doubled parameter of $Y_m$ (`New.Data.sortedParamY`). This parameter consists of the block $[k-1]$, then, for $i = 1, 2, \dots$, the entry $-(\kappa_i - \Delta/2)$ followed by the block $-\kappa_i + [t]$. Its entries at the positions $p < k - 1$ and $p = n_j - 1$ are twice the target parameters of [data and sizes](/chapter/data-and-sizes/) (`New.Data.sortedParamY_n_sub_one`).

Lean: `New.Data.keptColumns` (New/UpperBound/Objects/Weights.lean).

Lean: `New.Data.columnsY` (New/UpperBound/Objects/Weights.lean).

Lean: `New.Data.weightY` (New/UpperBound/Objects/Weights.lean).

**Theorem (Interlacing).** Write $\mu = \mu(X_m)$ and $\mu' = \mu(Y_m)$ at $\tau$. For all $p$,
$$\mu'_p = \mu_{p+1} + \mathrm{kept}(p+1), \qquad \mathrm{kept}(u) \le c_\tau(u).$$
So $\mu_p \ge \mu'_p \ge \mu_{p+1}$. For $p < n_m - 1$, $\mu'_p = \ell_m + \sum_{p < u < n_m - 1} c'_\tau(u)$. For $u \ge k$, $c'_\tau(u) \le \Delta$.

Lean: `New.Data.weightY_eq_weightX_add` (New/UpperBound/Objects/Weights.lean).

Lean: `New.Data.keptColumns_le_columnCount` (New/UpperBound/Objects/Weights.lean).

Lean: `New.Data.weightY_eq` (New/UpperBound/Objects/Weights.lean).

Lean: `New.Data.columnsY_le` (New/UpperBound/Objects/Weights.lean).

*Proof.* The first identity says $2\lambda'_p - 2\lambda_{p+1} - 1 = 2\,\mathrm{kept}(p+1)$ (`New.Data.sortedParamY_sub_paramX`), as $2[n_m - 1]_p = 2[n_m]_{p+1}$. This is a check, block by block. In a block of $Y_m$ the entries of $-\kappa_i + [t]$ sit one step to the left of the entries of $-\kappa_i + [t+1]$ in $X_m$, and they differ by $1/2$. At the position $n_j - 1$ the entry $-\kappa_{j+1} + \Delta/2$ of $Y_m$ faces the entry $-\kappa_{j+1} + t/2$ of $X_m$, and the difference less $1/2$ is $\Delta/2 - (t+1)/2$. The inequality $\mathrm{kept}(u) \le c_\tau(u)$ holds as $\Delta/2 - (t+1)/2 \le \Delta - (t+1)$ and, at $u = k$, as $\kappa_1 \ge 3\Delta/2$ and $k + t + 1 \le \Delta/2$. Then $\mu'_p - \mu_{p+1} = \mathrm{kept}(p+1) \ge 0$, and $\mu_p - \mu'_p = c_\tau(p+1) - \mathrm{kept}(p+1) \ge 0$. The formula for $\mu'_p$ follows from part (2) of the proposition: the kept counts telescope in $\sum c'_\tau$, and $\mathrm{kept}(n_m - 1) = 0$. Last, $c'_\tau(u)$ is a kept count, at most $\Delta/2$, plus a count of shortened columns of height $u + 1 > k$, which is also at most $\Delta/2$. $\square$

### The exponent of branching

The restriction to $Y_m$ in Section 7 multiplies by a power of a scalar. The power is the difference of the sizes of the two weights, $n_\tau = |\mu(X_m)| - |\mu(Y_m)|$, where $|\mu|$ is the sum of the entries.

**Proposition.** $n_\tau = a_\tau - m\Delta/2$. Summed over the $f$ infinite places, $\sum_\tau n_\tau = \#\Phi_a\, a - f m \Delta/2$, where $\Phi_a$ is the set of $a$-places.

Lean: `New.Data.branchExponent` (New/UpperBound/Objects/Weights.lean).

Lean: `New.Data.branchExponent_eq` (New/UpperBound/Objects/Weights.lean).

Lean: `New.Data.sum_branchExponent` (New/UpperBound/Objects/Weights.lean).

*Proof.* The blocks $[n]$ sum to $0$, so $2n_\tau$ is the sum of the doubled parameters of $X_m$ less that of $Y_m$. The first sum is $2a_\tau - 2(t+1)\sum_{i=1}^m \kappa_i$. The second is $-2\sum_{i=1}^m (\kappa_i - \Delta/2) - 2t\sum_{i=1}^m \kappa_i$. The difference is $2a_\tau - m\Delta$. The second claim is the sum over $\tau$, computed in $\mathbb{R}$. $\square$

### A worked example

The following numbers do not come from admissible data. They show the arithmetic at a small size. Take $k = 2$, $t = 3$, $\Delta/2 = 10$, $\Delta = 20$, $m = 2$, $\kappa(\tau) = 1$, and $\tau$ not an $a$-place. Then $\kappa_1 = 31$, $\kappa_2 = 51$, and $n_0, n_1, n_2 = 2, 6, 10$. The column counts are $c(2) = 31 - 3 = 28$ and $c(6) = 20 - 4 = 16$, and all others below $10$ are $0$.

The weights are $\mu(X_0) = (0, 0)$ and $\mu(X_1) = (-2, -2, -30, -30, -30, -30)$, with $\ell_1 = 1 - 31$. The diagrams are $\mu^+_1 = (28, 28)$ and $\mu^+_2 = (44, 44, 16, 16, 16, 16)$. With $\ell_2 = 3 - 51 = -48$,
$$\mu(X_2) = (-4, -4, -32, -32, -32, -32, -48, -48, -48, -48).$$
Eight columns are kept at the heights $2$ and $6$, so
$$\mu(Y_2) = (-4, -24, -32, -32, -32, -40, -48, -48, -48).$$
Its columns are $20$ of height $1$, $8$ of height $2$, $8$ of height $5$ and $8$ of height $6$, as the formula for $c'$ gives. The two weights interlace. The sums are $-328$ and $-308$, so $n_\tau = -20 = 0 - 2 \cdot 10$.

**Remark (Formalization).** The weights are functions on all of $\mathbb{N}$, not sequences of a fixed length. Only the entries $p < n_j$ of `New.Data.weightX j τ` and $p < n_m - 1$ of `New.Data.weightY τ` carry meaning; the others are junk values, and every lemma that uses them states the range. The subtractions in `New.Data.columnCount` and `New.Data.columnsY` are in $\mathbb{N}$; the lemmas above show that they do not truncate in the cases that matter.
