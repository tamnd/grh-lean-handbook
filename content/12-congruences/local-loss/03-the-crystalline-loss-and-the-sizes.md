---
title: The crystalline loss and the sizes
lean:
  - New/Congruences/LocalLoss/CrystallineCocycles.lean
decls:
  - New.Selmer.le_crystallineLoss_of_pow_dvd
  - New.Selmer.two_mul_lt_mul_crystallineLoss_succ
  - New.Selmer.cube_le_crystallineLoss_of_dvd
  - New.Selmer.natLog_lt_of_two_mul_log_lt
  - New.Selmer.noMultipleNear_of_forall_not_dvd
  - New.Selmer.CrystallineSizes
  - New.Selmer.HasFewLowJumps
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The crystalline loss and the sizes

The bound of [Section 4](/chapter/local-loss/#three-regimes-of-the-prime) is stated for abstract sizes $(Q, m, h, G, b, \delta, \eta, W)$ that satisfy a list of scale conditions. This section states the conditions and proves the arithmetic of the crystalline loss that the three regimes use. All results here are elementary. Their role is to say exactly which properties of the loss $\lambda$ and of the sizes enter the proof.

### Windows and gaps

We recall two notions of [side points](/chapter/exponent-lattices/#side-points). Let $\eta, b, W \in \mathbb{N}$ and $\varepsilon = \pm 1$. A finite set $U \subset \mathbb{Z}$ *fits the windows* $(\eta, \varepsilon, b, W)$ if every $u \in U$ lies in the *low window* $[-\eta, \eta]$ or in the *far window* $\varepsilon \cdot [b, b + W]$. For $p, n \in \mathbb{N}$ and $a \in \mathbb{Z}$, the *gap condition* $\mathrm{NoMult}(p, n, a)$ says that $p$ divides no nonzero integer $y$ with $|y| \leq n$, $|y - a| \leq n$ or $|y + a| \leq n$.

In the argument, $U$ is a set of jumps. The low window holds the small jumps, and the far window holds the jumps near a lift weight, with the sign of the embedding. The gap condition is what the cup product bounds of [cup products](/chapter/cup-products/) need for the defect to vanish: no multiple of $p$ near the jumps.

### The crystalline loss

Recall from [weights, signs and b-places](/chapter/main-summands/#weights-signs-and-b-places) that, for $h, b, \ell \in \mathbb{N}$,
$$\mathrm{crysLoss}(h, b, \ell) = v_\ell\big(N(h, b)\big), \qquad N(h, b) = (2b)! \cdot \Big(\prod_{n \in (b - 30h^3,\ b + 30h^3]} n\Big)^{h^3},$$
where $b - 30h^3$ is truncated at $0$, so that all $n$ are positive. Three properties of this number are used, and nothing else.

**Lemma (Divisors of the loss).** If $\ell$ is prime and $\ell^n \mid N(h, b)$, then $n \leq \mathrm{crysLoss}(h, b, \ell)$.

Lean: `New.Selmer.le_crystallineLoss_of_pow_dvd` (New/Congruences/LocalLoss/CrystallineCocycles.lean).

*Proof.* $N(h, b)$ is a product of positive integers, so it is not $0$. For a nonzero integer, $\ell^n$ divides it if and only if $n$ is at most its $\ell$-adic valuation. $\square$

**Lemma (The loss controls $2b/\ell$).** For every prime $\ell$ and all $h, b$,
$$2b < \ell\,\big(\mathrm{crysLoss}(h, b, \ell) + 1\big).$$

Lean: `New.Selmer.two_mul_lt_mul_crystallineLoss_succ` (New/Congruences/LocalLoss/CrystallineCocycles.lean).

*Proof.* By Legendre's formula, $v_\ell((2b)!) = \sum_{i \geq 1} \lfloor 2b/\ell^i \rfloor \geq \lfloor 2b/\ell \rfloor$. Since $\ell^{v_\ell((2b)!)}$ divides $N(h, b)$, the previous lemma gives $v_\ell((2b)!) \leq \lambda$. So $2b < \ell(\lfloor 2b/\ell \rfloor + 1) \leq \ell(\lambda + 1)$. $\square$

**Lemma (A multiple in the window).** If $\ell$ divides some $n \in (b - 30h^3, b + 30h^3]$, then $h^3 \leq \mathrm{crysLoss}(h, b, \ell)$.

Lean: `New.Selmer.cube_le_crystallineLoss_of_dvd` (New/Congruences/LocalLoss/CrystallineCocycles.lean).

*Proof.* $\ell$ divides the product over the window, so $\ell^{h^3}$ divides its $h^3$-th power, and so divides $N(h, b)$. Apply the first lemma. $\square$

The three lemmas split the primes into the regimes of Section 4. The second says that $\lambda$ is at least about $2b/\ell$; so if $\lambda$ is small, $\ell$ is large. The third says: if $\lambda < h^3$, then $\ell$ divides no integer in the window $(b - 30h^3, b + 30h^3]$. This is the gap condition near $b$.

**Example.** Take $\ell = 5$, $h = 1$ and $b = 3$. The window is $(0, 33]$, so $N = 6! \cdot 33!$. Here $v_5(6!) = 1$ and $v_5(33!) = 6 + 1 = 7$, so $\lambda = 8$. The second lemma reads $6 < 45$. The third applies with $n = 5$ and gives $1 \leq 8$. For a prime $\ell > 2b + 30h^3$, no factor of $N$ is divisible by $\ell$, so $\lambda = 0$; the second lemma then reads $2b < \ell$.

### Two elementary lemmas

**Lemma (A logarithm below $m$).** Let $\ell$ be prime and $H, b, m \in \mathbb{N}$. If $2\log(4b) < m$ and $H \leq 4b$, then $\lfloor \log_\ell H \rfloor < m$.

Lean: `New.Selmer.natLog_lt_of_two_mul_log_lt` (New/Congruences/LocalLoss/CrystallineCocycles.lean).

*Proof.* Since $\log x \geq 1 - 1/x$ for $x > 0$, we get $\log \ell \geq \log 2 \geq 1/2$. So $\lfloor \log_\ell H \rfloor \leq \log_\ell(4b) = \log(4b)/\log \ell \leq 2\log(4b) < m$. $\square$

**Lemma (Gap from no divisor).** Let $\ell, n, G, b, c, \delta, a \in \mathbb{N}$. Suppose $G + \delta + n < \ell$, $\delta + n < c$, and $\ell$ divides no integer in $(b - c, b + c]$. If $a = b + \delta$ or $a = G + \delta$, then $\mathrm{NoMult}(\ell, n, a)$ holds.

Lean: `New.Selmer.noMultipleNear_of_forall_not_dvd` (New/Congruences/LocalLoss/CrystallineCocycles.lean).

*Proof.* Let $y \neq 0$ be a multiple of $\ell$. Then $|y| \geq \ell$. We show that $|y|$ cannot be within $n$ of $0$ or of $a$. If $|y| \leq n$, then $\ell \leq n < \ell$. If $a = G + \delta$ and $||y| - a| \leq n$, then $\ell \leq |y| \leq G + \delta + n < \ell$. If $a = b + \delta$ and $||y| - a| \leq n$, then $|y| \in [b + \delta - n, b + \delta + n] \subset (b - c, b + c]$, since $\delta + n < c$. But $\ell$ divides $|y|$, against the hypothesis. The conditions $|y \mp a| \leq n$ imply $||y| - a| \leq n$, so all cases are covered. $\square$

### The size conditions

**Definition (Crystalline sizes).** Natural numbers $Q, m, h, G, b, \delta, \eta, W$ are *crystalline sizes* if

1. $0 < Q$;
2. $99\,(Q^2 + (W+1)Q + Q + W + m) \leq h$;
3. $99\,h^3 \leq G$;
4. $99\,(G h^3 + G) \leq b$;
5. $2 \log(4b) < m$, in the real numbers;
6. $\delta < \eta$;
7. $99\,((\eta + W)Q + \eta + h) \leq h^3$.

Lean: `New.Selmer.CrystallineSizes` (New/Congruences/LocalLoss/CrystallineCocycles.lean).

Read $A \ll B$ as $99A \leq B$. The conditions say $Q^2 \ll h$, $h^3 \ll G$, $h^3 G \ll b$, $\log b \ll m$ and $Q\eta \ll h^3$, with room for the width $W$ and the shift $\delta$. In the argument, $Q = kt$ bounds the small primes, $h$ is the half gap, $G$ is the weight off the b-places, $b$ is the weight at the b-places, $\eta = h^2 + 1$ is the radius of the low window and $W = 4t$ is the width of the far windows. [Section 5](/chapter/local-loss/#the-defect-at-a-place-above) proves that the data satisfy these conditions.

Two consequences are used often. From 3 and 7, $\eta \leq h^3 \leq G$, and $\delta + W \leq \eta + W \leq h^3 \leq G$. So the low window and the far windows of width $W$ at $G + \delta$ lie in $[-2G, 2G]$. From 2, $m \leq h$ and $Q \leq h$.

**Remark (Formalization).** Condition 5 is the only condition stated in the real numbers. The source uses it only through the lemma on logarithms above, which turns it into $\lfloor \log_\ell H \rfloor < m$ for $H \leq 4b$. The constant $99$ is generous. The proofs in the source use each condition as a linear inequality, so the exact constant does not matter as long as it is large.

### Few low jumps

**Definition (Few low jumps).** Let $L$ be a lattice over $O$, $h, \mu, \eta \in \mathbb{N}$, and $U, U'$ assign a finite set of integers to each map $\gamma : O \to \mathbb{C}_\ell$. Then $L$ has *few low jumps* for $(h, \mu, \eta, U, U')$ if

1. for each $\gamma$ and each $u < 0$ with $u \in U(\gamma)$ or $u \in U'(\gamma)$, $2u \leq -h$;
2. for each $\gamma$, $\sum_{u \in [-\eta, \eta]} \mathrm{jump}(L, \gamma, u) \leq \mu$.

Lean: `New.Selmer.HasFewLowJumps` (New/Congruences/LocalLoss/CrystallineCocycles.lean).

Condition 1 says that negative jumps are far from $0$, at distance at least $h/2$. Condition 2 bounds the number of jumps in the low window, with multiplicity. In the third regime the defect is $0$ when there are no negative jumps near $0$, and condition 2 bounds the defect in the remaining case. For a main summand, $\mu$ is $\lfloor rm/k \rfloor$, by the third condition of the main summand weights; see [Section 5](/chapter/local-loss/#the-defect-at-a-place-above).
