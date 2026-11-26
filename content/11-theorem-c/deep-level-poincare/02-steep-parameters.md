---
title: Steep parameters of Y₀ and its extension
lean:
  - New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean
decls:
  - New.Data.abs_targetParameter_sub_lowestKType_le_and_eq
  - New.Data.exists_isSteep
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Steep parameters of Y₀ and its extension

The vanishing criterion of Section 5 needs a lower bound for a local pairing at each real place. [Laplace's method](/chapter/laplace-method/) gives this bound for steep parameters (one line: if the parameter of $U(n)$ is steep, the restriction to $U(n-1)$ of the matrix coefficient has a pairing that is not too small, [the restriction theorem](/decl/New.DiscreteSeries.IsSteep.exists_volume_le_mul_norm_integral_dsCoeff/)). This section shows that the parameter of $Y_0$, and minus the parameter of $\tilde Y^0_0 = Y_0 \oplus E\tilde e$, are steep at every infinite place.

### The data

We use the data $D$ of [the outline of Theorem C](/chapter/theorem-c-plan/). Let $r$ be the rank of $Y_m$, $m$ the number of lifts and $k = r + 1 - m$ the rank of the source. The number $m$ is even and $k$ is even ([the data and their sizes](/chapter/data-and-sizes/)). Write $\varrho = m/2 - 1$ for the number of hyperbolic planes of $Y_0$. Let $\Delta = 2r^8$ be the gap and $\kappa$ the weight. At an infinite place $\tau$ the lift weights are $\kappa_j(\tau) = \kappa(\tau) + (j + 1/2)\Delta$ ([liftWeight](/decl/New.Data.liftWeight/)). Write $B = \kappa_0(\tau)$. The data give $\Delta^2 \leq B$.

The *row parameter* at $\tau$ is the sequence $t_0, t_1, \dots$ with

$$t_i = \frac{k}{2} - 1 - i \quad (i + 1 < k), \qquad t_i = \frac{\Delta}{2} - \kappa_{i+2-k}(\tau) \quad (i + 1 \geq k).$$

The entries with $i + 1 < k$ are the *near entries*. The others are the *far entries*. The near entries lie in $[1 - k/2, k/2 - 1]$. Every far entry is at most $\Delta/2 - \kappa_1 < -B$. So every far entry lies below every near entry, and the far entries strictly decrease, with steps $\Delta$.

The index set of the node $(0,0)$ of the grid $Y$ (for $z = \text{false}$) or $\tilde Y$ (for $z = \text{true}$) has $N = r + z$ elements. Here $z$ is read as $0$ or $1$. The source numbers these indices by a bijection $\nu$ onto $\{0, \dots, N-1\}$ (`New.Data.gridNumber`). For $z = \text{true}$ the extra index $\tilde e$ gets the number $r$. The doubled parameter at $\tau$ is $l(y) = 2t_{\nu(y)} + z$, and the sign of $y$ is $\varepsilon(y) = (-1)^{\nu(y) + 1 - k}$ for a far entry and $+1$ for a near entry ([the grids](/chapter/upper-bound-objects/), `New.Data.gridParam` and `New.Data.gridSigns`). For $z = \text{true}$ this is minus twice the parameter of $\tilde Y^0_0$, up to the shift by $1$ that makes the entries congruent to $N - 1$ modulo $2$.

The weight of the lowest $K$-type is $\Lambda = \lambda + \rho_n - \rho_c$ ([Blattner's formula](/chapter/discrete-series/), [two_mul_lowestKType](/decl/New.two_mul_lowestKType/)). For the doubled parameter $l = 2\lambda$ this reads

$$2\Lambda(y) = l(y) + 2\rho_n(y) - 2\rho_c(y),$$

where $2\rho_c(y)$ is the number of indices $y'$ with $\varepsilon(y') = \varepsilon(y)$ and $l(y') < l(y)$, minus the number with $l(y') > l(y)$, and $2\rho_n(y)$ is the same count over indices with $\varepsilon(y') \neq \varepsilon(y)$.

### The count lemma

**Lemma (The signed count).** Let $\tau$ be an infinite place. Let $\nu$ be a numbering of the $N = r + z$ indices of the node $(0,0)$ such that, for every index $x$, the sign of $x$ is $\mathrm{entrySign}_{0,0}(\nu(x) + 1 - k)$ and the doubled parameter is $2t_{\nu(x)} + z$. For an index $y$ put

$$L = 2t_{\nu(y)} + z - 2\Lambda(y).$$

Then $|L| \leq N$. If $y$ is a near entry, that is $\nu(y) + 1 < k$, then

$$L + N = N + \min(N, k) - 1 - 2\nu(y) - ((N - k) \bmod 2).$$

The subtraction $\nu(x) + 1 - k$ is in the natural numbers, so it is $0$ on the near entries.

Lean: `New.Data.abs_targetParameter_sub_lowestKType_le_and_eq` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

*Proof.* Write $a = \nu(y)$. For a number $i$ put

$$c(a, i) = \operatorname{sgn}(t_a - t_i) \cdot \begin{cases} 1 & \text{if } (i + 1 - k) \equiv (a + 1 - k) \pmod 2, \\ -1 & \text{otherwise.} \end{cases}$$

The sign $\mathrm{entrySign}_{0,0}(i)$ depends only on the parity of $i$, and it takes both values. So the second factor is $+1$ exactly when the indices numbered $i$ and $a$ have the same sign. By the formula for $2\Lambda$, the number $L = l(y) - 2\Lambda(y) = 2\rho_c(y) - 2\rho_n(y)$ is the sum of $c(a, i)$ over $i = 0, \dots, N - 1$. Each term is $-1$, $0$ or $1$. So $|L| \leq N$.

Let $a$ be a near entry. We prove by induction on $M$ that

$$\sum_{i < M} c(a, i) + M = M + \min(M, k) - 1 - 2a - ((M - k) \bmod 2)$$

for every $M \geq 0$, with the right side read in the natural numbers, so that a negative difference is $0$. For $M = 0$ both sides are $0$. In the step from $M$ to $M + 1$ we add the term $c(a, M)$. There are three cases.

1. If $M + 1 < k$, then $M$ is a near entry, of sign $+1$, like $a$. The term is $1$ if $M > a$ (as $t_M < t_a$), $-1$ if $M < a$, and $0$ if $M = a$.
2. If $M + 1 = k$, then $M$ is the first far entry. Its sign is $+1$ and $t_M < t_a$. The term is $1$.
3. If $M + 1 > k$, then $M$ is a far entry and $t_M < t_a$. The term is $(-1)^{M + 1 - k}$.

The sum of the near terms over $i < \min(M, k - 1)$ is the number of $i$ with $a < i < \min(M, k-1)$, minus $\min(M, a)$. The far terms alternate $1, -1, 1, \dots$, so their sum is $1$ if the number $M - k + 1$ of far terms is odd and $0$ otherwise. Adding these gives the formula, as the source checks case by case. For $M = N$ we get the claim. $\square$

The near formula with $N \geq k$ reads $L = k - 1 - 2a - ((N - k) \bmod 2)$.

### The steepness theorem

**Theorem (Steep parameters).** For $z \in \{\text{false}, \text{true}\}$ there is a bijection

$$e : \mathrm{InitIndex}_0 \sqcup \{0, \dots, 2\varrho + 1 + z\} \to \mathrm{GridIndex}_z(0,0)$$

such that for every infinite place $\tau$ the doubled parameter $l = \mathrm{gridParam}_z(0,0,0,\tau)$ is steep for $(B, e)$ with $B = \kappa_0(\tau)$ ([IsSteep](/decl/New.DiscreteSeries.IsSteep/)). Here $\mathrm{InitIndex}_0$ is the set of basis indices of $X_0$ other than the last. It has $k - 1$ elements. In words: on $\mathrm{InitIndex}_0$ the sign is $+1$ and the weight of the lowest $K$-type is $0$; on the other $2\varrho + 2 + z$ indices the signs alternate, beginning with $+1$, and the weight strictly decreases and lies in $[-3B, -B]$.

Lean: `New.Data.exists_isSteep` (New/Determinant/AuxiliaryForms/DeepLevelPoincarePeriod.lean).

[The Bessel functions at a real place](/chapter/bessel-real-place/) uses this theorem in Volume 10.

*Proof.* Let $\nu$ be the numbering `gridNumber` of the indices. The counts match: $(k - 1) + (2\varrho + 2 + z) = k - 1 + m + z = r + z = N$. Let $e$ send $x \in \mathrm{InitIndex}_0$ to $\nu^{-1}(x)$ and $i$ to $\nu^{-1}(k - 1 + i)$. So $e$ sends $\mathrm{InitIndex}_0$ to the near entries and the second block to the far entries, in order. The definitions of `gridSigns` and `gridParam` at the node $(0,0)$ give the hypothesis of the count lemma: the sign of $x$ is $\mathrm{entrySign}_{0,0}(\nu(x) + 1 - k)$ and the doubled parameter is $2t_{\nu(x)} + z$. Fix $\tau$ and write $\Lambda$ for the lowest $K$-type of $l$. We check the five conditions of steepness.

*Signs.* On a near entry the sign is $\mathrm{entrySign}_{0,0}(0) = 1$. The far entry $e(i)$ has sign $\mathrm{entrySign}_{0,0}(i) = (-1)^i$.

*Weight zero on the near entries.* Let $y = e(x)$ with $a = \nu(y) < k - 1$. As $m \geq 1$, $N = r + z \geq k$, so $\min(N, k) = k$. The count lemma gives $L = k - 1 - 2a - ((N - k) \bmod 2)$. Here $N - k = m - 1 + z$ and $m$ is even, so $(N - k) \bmod 2 = 1 - z$. Hence $L = k - 2 - 2a + z$. The doubled parameter is $2t_a + z = k - 2 - 2a + z$. So $2\Lambda(y) = 2t_a + z - L = 0$.

*Bounds on the far entries.* Let $y = e(i)$, so $\nu(y) = k - 1 + i$ and $t_{\nu(y)} = \Delta/2 - \kappa_{i+1}$. Then

$$2\Lambda(y) = \Delta - 2\kappa_{i+1} + z - L, \qquad \kappa_{i+1} = B + (i + 1)\Delta.$$

The count lemma gives $|L| \leq N \leq r + 1$, and $r + 2 \leq \Delta$. So $2\Lambda(y) \leq \Delta - 2B - 2\Delta + 1 + r + 1 \leq -2B$, that is $\Lambda(y) \leq -B$. For the lower bound, $i + 1 \leq m + 1 \leq \Delta$, so $\kappa_{i+1} \leq \kappa_\Delta = B + \Delta^2 \leq 2B$, by $\Delta^2 \leq B$. So $2\Lambda(y) \geq \Delta - 4B - (r + 1) \geq -6B$, that is $\Lambda(y) \geq -3B$.

*Strict decrease.* For $i < i'$ the difference $2\Lambda(e(i)) - 2\Lambda(e(i'))$ is $2(i' - i)\Delta$ minus a difference of two counts. The counts differ by at most $2N \leq 2r + 2 < 2\Delta$. So the difference is positive. $\square$

**Remark (Formalization).** The theorem fixes one bijection $e$ for all infinite places. This works because the numbering $\nu$ does not depend on $\tau$. The source proves the bounds and the signs by the tactic `grind` from the formula `New.Data.targetParameter_eq` and the parities above. It does not write out the case analysis. The three-way sign in the count is written with `if` in the source. The bound $|L| \leq N$ is what is used. The sharper bound $|L| \leq N - 1$ also holds, since the term $i = a$ is $0$.

### An example of steep parameters

Let $r = 3$ and $m = 2$. Then $k = 2$, $\varrho = 0$ and $\mathrm{InitIndex}_0$ has one element. Take $z = \text{false}$. The row parameter is $t_0 = 0$, $t_1 = \Delta/2 - \kappa_1$, $t_2 = \Delta/2 - \kappa_2$. The signs are $+, +, -$. For the far entry numbered $1$, the index $0$ lies above it with the same sign and the index $2$ lies below it with the other sign. So $2\rho_c = -1$ and $2\rho_n = 1$, and $2\Lambda = 2t_1 + 2 = \Delta - 2\kappa_1 + 2$. For the near entry, both other indices lie below it, one of each sign. So $2\rho_c = 2\rho_n = 1$ and $2\Lambda = 0$. The far weights $2\Lambda = \Delta - 2\kappa_1 + 2$ and $\Delta - 2\kappa_2 - 2$ decrease and lie in $[-6B, -2B]$.
