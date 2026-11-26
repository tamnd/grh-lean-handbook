---
title: Rows and one kernel
lean:
  - New/UpperBound/Size/Estimates.lean
  - New/UpperBound/Size/ArchimedeanSize.lean
decls:
  - New.Data.rowMainLength
  - New.Data.rowSlack
  - New.Data.diagramWeight_le_rowMainLength_add_rowSlack
  - New.Data.rowMainLength_add_rowSlack_le
  - New.Data.norm_map_star_piMBar_sq
  - New.Data.jetSize_le_add
  - New.Data.rowSizeSum
  - New.Data.sqrt_weylNormSq_jetMap_le
  - New.Data.jetSize_zero
  - New.Data.sum_range_jetSize_add_eq
  - New.Data.chainSize
  - New.Data.sum_rowSizeSum_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Rows and one kernel

The lift from $X_j$ to $X_{j+1}$ has a weight, and the weight has a Young diagram at each infinite place $\tau$. The bound for the jets of one kernel is a sum of $s_\infty(l)$ over the row lengths $l$ of these diagrams. This section bounds each row by a main length plus a slack, bounds one kernel, and adds the row sizes over the $m$ lifts.

Recall the jet size ([the prime sums](/chapter/prime-sums/); Lean: `New.Data.jetSize`)
$$s_\infty(l) = \log l! + l\log(M/\Omega),$$
and the bounds $20\,l\log b \le s_\infty(l) \le 25\,l\log b$ for $l \le a$ (`New.Data.jetSize_mem_Icc`). Here $20\log b \le \log(M/\Omega) \le 23\log b$.

### The rows of a lift diagram

Let $j < m$. The diagram of the lift $j + 1$ at $\tau$ has $c_\tau(h)$ columns of height $h$ for $h < n_{j+1}$. Its row $i$, counted from $0$, has length $\mu^+_{j+1,i}(\tau)$ ([weights and lift diagrams](/chapter/upper-bound-objects/#weights-and-lift-diagrams)). The same chapter proves the row bounds: row $0$ is at most $a_\tau + \kappa_{j+1}(\tau)$, a row $0 < i < k$ is at most $\kappa_{j+1}(\tau)$, and a row $i \ge k$ is at most $m\Delta$ (`New.Data.liftDiagram_le`). Here $\kappa_{j}(\tau) = \kappa(\tau) + j\Delta + \Delta/2$ is the lift weight (`New.Data.liftWeight_eq`), $\Delta = 2r^8$, and $\Delta/2 = r^8$.

**Definition (Main length and slack).** The main length of row $i$ at $\tau$ is
$$\ell_\tau(i) = \begin{cases} c_\tau(1) = a_\tau & i = 0,\\ \kappa(\tau) & 0 < i < k,\\ 0 & i \ge k.\end{cases}$$
The slack of row $i$ is
$$\mathrm{sl}(i) = \begin{cases} b + \lfloor a/\lfloor x_1\rfloor\rfloor + (\Delta/2)^2 & i = 0,\\ (\Delta/2)^2 & i > 0.\end{cases}$$

Lean: `New.Data.rowMainLength`, `New.Data.rowSlack` (New/UpperBound/Size/Estimates.lean).

The number $\lfloor a/\lfloor x_1\rfloor\rfloor$ is the weight off $\Phi_b$ (`New.Data.offWeight`). Every weight is $b$ or this number, so $\kappa(\tau) \le b + \lfloor a/\lfloor x_1\rfloor\rfloor$ (`New.Data.weight_le_natB_add_offWeight`).

**Lemma (Rows of a lift diagram).** For $j < m$, every place $\tau$ and every $i$, row $i$ of the diagram of lift $j + 1$ at $\tau$ is at most $\ell_\tau(i) + \mathrm{sl}(i)$.

Lean: `New.Data.diagramWeight_le_rowMainLength_add_rowSlack` (New/UpperBound/Size/Estimates.lean).

*Proof.* The row of the diagram with column counts $c_\tau(h)$, $h < n_{j+1}$, is the row $\mu^+_{j+1,i}(\tau)$ (`New.Data.cast_diagramWeight_columnCount`). As $j + 1 \le m$,
$$\kappa_{j+1}(\tau) \le \kappa(\tau) + m\Delta + \Delta/2 .$$
The table of sizes gives $m\Delta + \Delta/2 \le (\Delta/2)^2$: indeed $\Delta/2 = r^8$ has degree $40$ in $x$ and $m \le 2\sqrt x$. Now take the three ranges of $i$.

- $i = 0$: the row is at most $a_\tau + \kappa_{j+1}(\tau) \le a_\tau + \kappa(\tau) + (\Delta/2)^2 \le a_\tau + b + \lfloor a/\lfloor x_1\rfloor\rfloor + (\Delta/2)^2$.
- $0 < i < k$: the row is at most $\kappa_{j+1}(\tau) \le \kappa(\tau) + (\Delta/2)^2$.
- $i \ge k$: the row is at most $m\Delta \le (\Delta/2)^2$.

In each case this is $\ell_\tau(i) + \mathrm{sl}(i)$. $\square$

**Lemma (Rows are at most $2a$).** $\ell_\tau(i) + \mathrm{sl}(i) \le 2a$ for every $\tau$ and $i$.

Lean: `New.Data.rowMainLength_add_rowSlack_le` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* The table of sizes gives $b + \lfloor a/\lfloor x_1\rfloor\rfloor + (\Delta/2)^2 \le a$, since $a = xb$. So $\mathrm{sl}(i) \le a$. The main length is $a$ or $0$ for $i = 0$, and $\kappa(\tau) \le b + \lfloor a/\lfloor x_1\rfloor\rfloor \le a$ for $0 < i < k$. So $\ell_\tau(i) \le a$ too. $\square$

### Two small facts

**Lemma (The norm of $\bar\pi_M$).** Let $\bar\pi_M$ be the integer of $K$ with $\bar\pi_M\cdot\overline{\bar\pi_M} = M$. Then $|\sigma(\overline{\bar\pi_M})|^2 = M$ for every automorphism $\sigma$ of $\mathbb C$.

Lean: `New.Data.norm_map_star_piMBar_sq` (New/UpperBound/Size/Estimates.lean).

*Proof.* Let $\iota = \sigma\circ\bar{\ }$, a ring map $K \to \mathbb C$. Its image is $K$ or its conjugate, and in both cases $|\iota(\bar z)| = |\iota(z)|$ for $z \in K$, since $\iota$ restricted to $K$ is the identity or complex conjugation, followed by an embedding. So
$$|\sigma(\overline{\bar\pi_M})|^2 = |\iota(\bar\pi_M)|\,|\iota(\overline{\bar\pi_M})| = |\iota(\bar\pi_M\overline{\bar\pi_M})| = |\iota(M)| = M. \qquad\square$$

**Lemma (Jet size of a longer row).** Let $l \le r + e$ be natural numbers. Then
$$s_\infty(l) \le s_\infty(r) + e\bigl(\log(r + e + 1) + \log(M/\Omega)\bigr).$$

Lean: `New.Data.jetSize_le_add` (New/UpperBound/Size/Estimates.lean).

*Proof.* First, $l! \le (r + e)! = r!\,(r + 1)(r + 2)\cdots(r + e) \le r!\,(r + e + 1)^e$. Take logarithms: $\log l! \le \log r! + e\log(r + e + 1)$. Second, $\log(M/\Omega) \ge 0$, so $l\log(M/\Omega) \le (r + e)\log(M/\Omega)$. Add the two. $\square$

**Lemma.** $s_\infty(0) = 0$.

Lean: `New.Data.jetSize_zero` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* $\log 0! = \log 1 = 0$. $\square$

### One kernel

**Definition (Row size of a lift).** For $j < m$,
$$\mathrm{rowSize}_j = \sum_{\tau\in\Phi}\sum_{i<n_j}s_\infty\bigl(\mu^+_{j+1,i}(\tau)\bigr).$$

Lean: `New.Data.rowSizeSum` (New/UpperBound/Size/ArchimedeanSize.lean).

The sum runs over the first $n_j = \#X_j$ rows, because the Schur growth exponent of [archimedean bounds for jets](/chapter/theta-kernels-gauges/#archimedean-bounds-for-jets) sums over the rows $i < |n|$ of the source, here $n = X_j$.

**Theorem (One kernel).** Let $j < m$, $\sigma \in \mathrm{Aut}(\mathbb C)$, $t$ a translation, $g \in G_f(X_j)$ and $g' \in G_f(X_{j+1})$. Let $J$ be the jet map of the lift kernel of $X_j \to X_{j+1}$ for the trivial twist, applied to $\omega(g, g')$ of the translate of the normalized vacuum by $t$. Then for every vector $\xi$ of the Weyl module of $X_j$,
$$\|\sigma\circ J\xi\|_{\mathrm W} \le \exp\bigl(x^{50} + \tfrac12\mathrm{rowSize}_j\bigr)\,\|\sigma\circ\xi\|_{\mathrm W}.$$

Lean: `New.Data.sqrt_weylNormSq_jetMap_le` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* *The jet bound.* A single translate is a vacuum combination of size $1$ (`New.Parameters.isVacuumCombination_finHeisenbergOp`). Apply the theorem on the size of Schur jets of [archimedean bounds for jets](/chapter/theta-kernels-gauges/#archimedean-bounds-for-jets) with $B = 1$, $L = a + 1$, $c = \overline{\bar\pi_M}$ and the lift weight with column counts $c_\tau(h)$ (`New.Data.isLiftWeight_columnCount`). By the lemma on the norm of $\bar\pi_M$, $u = \log(|\sigma c|^2/\Omega) = \log(M/\Omega)$. With $\#X_j = n_j$ and $\#X_{j+1} = n_{j+1}$, the bound is $\exp(\mathrm{const} + \mathrm{count} + w)$, where
$$\mathrm{const} = C_P\bigl(q_1n_{j+1}n_j + 1\bigr)^2,\qquad \mathrm{count} = f\,n_{j+1}n_j\log\bigl(2(a+1) + 2\bigr),$$
and $w$ is the Schur growth exponent
$$w = \frac12\sum_\tau\sum_{i<n_j}\Bigl(\frac{l_{\tau,i}}{a+1} + \log l_{\tau,i}! + l_{\tau,i}\log\frac M\Omega\Bigr) = \frac12\bigl(\mathrm{lengths} + \mathrm{rowSize}_j\bigr),$$
with $l_{\tau,i} = \mu^+_{j+1,i}(\tau)$ and $\mathrm{lengths} = \sum_{\tau,i}l_{\tau,i}/(a+1)$.

*The other terms.* By the two lemmas on rows, $l_{\tau,i} \le 2a$, so $\mathrm{lengths} \le 2fn_j$. The table of sizes gives $q_1 \le x^{12}$, $f \le x^{12}$, $n_j \le n_{j+1} \le n_m \le e^{12}x^{11/2}$, $C_P \le \log x$ and $\log(2a + 4) \le 3\log b \le x$. So
$$\mathrm{const} \le \log x\,(e^{24}x^{23} + 1)^2,\quad \mathrm{count} \le e^{24}x^{24},\quad \mathrm{lengths} \le 2e^{12}x^{18},$$
and $\mathrm{const} + \mathrm{count} + \tfrac12\mathrm{lengths} \le x^{50}$. So the exponent is at most $x^{50} + \tfrac12\mathrm{rowSize}_j$. $\square$

**Remark (Formalization).** The bound of the theorem is on $\sqrt{\cdot}$ of the squared Weyl norm `weylNormSq`. The index $j$ is a bound variable, and `le_of_hasLogBound` needs a size for it. The proof gives it the instance $\log j \le \tfrac12\log x + 2$ from $j \le m$ (`New.Data.hasLogUpper_of_le`). The growth rate is $L = a + 1$ as a positive natural number, `D.a.succPNat`, so $L \ne 0$ and the division by $L$ is honest.

### The sum over the lifts

**Lemma (Main lengths and slacks of one diagram).** For every $\tau$ and $j$, with $\beta = 25\log b$,
$$\sum_{i<n_j}\bigl(s_\infty(\ell_\tau(i)) + \beta\,\mathrm{sl}(i)\bigr) = s_\infty(a_\tau) + (k - 1)s_\infty(\kappa(\tau)) + \beta\bigl(b + \lfloor a/\lfloor x_1\rfloor\rfloor + n_j(\Delta/2)^2\bigr).$$

Lean: `New.Data.sum_range_jetSize_add_eq` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* As $k \le n_j$, the rows $i < n_j$ are row $0$, the $k - 1$ rows $0 < i < k$, and the rows $k \le i < n_j$. Their main lengths are $a_\tau$, $\kappa(\tau)$ and $0$, and $s_\infty(0) = 0$. The slack adds $b + \lfloor a/\lfloor x_1\rfloor\rfloor$ once and $(\Delta/2)^2$ for each of the $n_j$ rows. $\square$

**Definition (Chain size).** The main term of the size of the chain is
$$\mathrm{chainSize} = m\Bigl(\#\Phi_a\,s_\infty(a) + k\sum_{\tau\in\Phi}s_\infty(\kappa(\tau))\Bigr).$$

Lean: `New.Data.chainSize` (New/UpperBound/Size/ArchimedeanSize.lean).

**Theorem (The rows of all lifts).**
$$\sum_{j<m}\mathrm{rowSize}_j \le \mathrm{chainSize} + \tfrac12 fa\log^3 b .$$

Lean: `New.Data.sum_rowSizeSum_le` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* *One box.* As $2a + 1 \le b^2$ and $\log(M/\Omega) \le 23\log b$,
$$\log(2a + 1) + \log(M/\Omega) \le 25\log b = \beta .$$

*One row.* Let $j < m$. By the lemma on rows, $l = \mu^+_{j+1,i}(\tau) \le \ell_\tau(i) + \mathrm{sl}(i)$. The lemma on longer rows, with $r = \ell_\tau(i)$ and $e = \mathrm{sl}(i)$, and the bound $r + e \le 2a$ give
$$s_\infty(l) \le s_\infty(\ell_\tau(i)) + \mathrm{sl}(i)\bigl(\log(2a + 1) + \log(M/\Omega)\bigr) \le s_\infty(\ell_\tau(i)) + \beta\,\mathrm{sl}(i).$$

*One lift.* Sum over $i < n_j$ and $\tau$, use the last lemma, and use $n_j \le n_m$:
$$\mathrm{rowSize}_j \le \mathrm{main} + \mathrm{slack},$$
with
$$\mathrm{main} = \sum_\tau s_\infty(a_\tau) + (k - 1)\sum_\tau s_\infty(\kappa(\tau)),\qquad \mathrm{slack} = f\beta\bigl(b + \lfloor a/\lfloor x_1\rfloor\rfloor + n_m(\Delta/2)^2\bigr).$$
Since $s_\infty(0) = 0$, $\sum_\tau s_\infty(a_\tau) = \#\Phi_a\,s_\infty(a)$.

*All lifts.* Sum over $j < m$: the left side is at most $m(\mathrm{main} + \mathrm{slack})$. Each $s_\infty(\kappa(\tau))$ is at least $20\kappa(\tau)\log b \ge 0$, so $(k - 1)\sum_\tau s_\infty(\kappa(\tau)) \le k\sum_\tau s_\infty(\kappa(\tau))$, and $m\cdot\mathrm{main} \le \mathrm{chainSize}$. Last,
$$m\cdot\mathrm{slack} = 25mf\log b\bigl(b + \lfloor a/\lfloor x_1\rfloor\rfloor + n_m(\Delta/2)^2\bigr) \le \tfrac12 fa\log^3 b,$$
since $m \le 2\sqrt x$, $a = xb$, and the bracket is at most $3b$: indeed $\lfloor a/\lfloor x_1\rfloor\rfloor \le b$ as $x \le x_1$, and $n_m(\Delta/2)^2$ has degree $85.5$ in $x$. So the left side is at most $150\sqrt x\,fb\log b$, far below $\tfrac12 xfb\log^3 b$. $\square$

The first row is the long one: it has $a$ boxes at an $a$-place, and its excess over $a$ is at most about $b$. The cost of this excess is $25\log b$ per box, so at most about $25b\log b$ per lift and place. Over the $m$ lifts and $f$ places this is about $50\sqrt x\,fb\log b$, while the error term is $\tfrac12 xfb\log^3 b$. So the slack is cheap.

### An example with one place

Take one place $\tau \in \Phi_a$, so $a_\tau = a$, and look at the first lift, $j = 0$. The main lengths are $a$, then $k - 1$ times $\kappa(\tau)$, then $0$. The row sizes add up to about $s_\infty(a) + (k - 1)s_\infty(\kappa(\tau))$. By the bounds $s_\infty(l) \approx 20l\log b$ to $25l\log b$, this is about $20(a + (k - 1)\kappa(\tau))\log b$. The theorem on one kernel then gives a factor of about $\exp(10(a + k\kappa(\tau))\log b)$ on the Weyl norm. The prime sums of the next section remove the main part of this factor.
