---
title: Three regimes of the prime
lean:
  - New/Congruences/LocalLoss/CrystallineCocycles.lean
decls:
  - New.Selmer.LettersReadThick
  - New.Selmer.fitsWindows_letterJumps
  - New.Selmer.CrystallineSizes.differentBound_mul_add_log_le
  - New.Selmer.LettersReadThick.hasCupExponent_of_le
  - New.Selmer.CrystallineSizes.hasCupExponent_of_cube_le
  - New.Selmer.CrystallineSizes.noMultipleNear
  - New.Selmer.normLength_dualDefect_le_of_noMultipleNear
  - New.Selmer.normLength_dualDefect_le_of_crystallineSizes
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Three regimes of the prime

This section proves the bound for the crystalline class at one place, for abstract sizes. Let $\lambda$ be the crystalline loss and $K = \lfloor 2\lambda/Q \rfloor$. The theorem says that the normalised dual defect is at most the index times $10^5(\mathrm{rank}\,L \cdot Km + \mu\lambda)$. The proof splits the prime $\ell$ into three regimes: $\ell \leq Q$; $\ell > Q$ with $\lambda \geq h^3$; and $\ell > Q$ with $\lambda < h^3$. Each regime uses one bound of [cup products](/chapter/cup-products/).

### Kummer charts and letters

We recall the language of [Kisin frames](/chapter/kisin-frames/#charts-and-kummer-charts). A *Kummer chart* $\kappa$ of $\Gamma$ has a ramification index $e$ and a residue degree $f$. Its *letters* are the units of $\mathbb{F}_{\ell^f}$. For a letter $i$, let $[i]$ be its Teichmüller lift and $\omega_i = \theta([i]) \in \mathbb{C}_\ell$, a root of unity of order dividing $\ell^f - 1$. The Frobenius on letters is $i \mapsto i^\ell$. The chart is *unramified* if $e = 1$ and its Eisenstein polynomial is $z + \ell$. Its *different bound* is $d = 0$ if $e = 1$ and $d = v_\ell(e) + 1$ otherwise. Fix $\zeta \in O$ with $\zeta^{\ell^f - 1} = 1$. For sets $U(\gamma)$ of integers, indexed by the maps $\gamma : O \to \mathbb{C}_\ell$, the *jump set at the letter* $i$ is
$$U_i = \{0\} \cup \bigcup_{\gamma : \gamma(\zeta) = \omega_i} U(\gamma).$$
So the letter of an embedding $\gamma$ is read from the value $\gamma(\zeta)$.

### Four bounds on cup products

We state once the four results of [cup products](/chapter/cup-products/) that this chapter uses. Let $j : \Gamma \to G_p$ be an open embedding, $\kappa$ a Kummer chart and $\zeta$ as above. Let $L$ be crystalline with jumps in $U'$, that is $L \in \mathrm{InClass}(\top, \bot, U')$, and write $\mathcal{Q} = \mathrm{InClass}(\top, \bot, U)$. In the first three results, $U_i$ fits the windows $(\eta, -\varepsilon_i, b_i, W)$ and $U'_i$ fits $(\eta, \varepsilon_i, b_i, W)$ at each letter $i$.

**Theorem (Generic primes).** Let $\kappa$ be unramified, $p \geq 5$ and $\eta \geq 1$. Suppose that at each letter $b_i + W + \eta \leq (p-3)a$, $6(a + \eta + W) < b_i$, and $\mathrm{NoMult}(p, 6(a + \eta + W), b_i)$. (a) If no member of any $U(\gamma)$ or $U'(\gamma)$ lies in $[-a, 0)$, or every $U'(\gamma) \subset [-\eta, 0]$, then $\delta_{\mathcal{Q}}(L) = 0$. (b) For every $\mu$, if $\sum_{u \in [-\eta, \eta]} \mathrm{jump}(L, \gamma, u) \leq \mu$ for each $\gamma$, then $\delta_{\mathcal{Q}}(L) \leq 11 f(\mu(a + 1) + \mathrm{rank}\,L\,(W+1)) \cdot \mathrm{length}(O/p)$.

Lean: `New.Lift.KummerChart.dualDefect_eq_zero_and_dualDefect_le` (New/Congruences/Lifting/CupOrthogonalityBounds.lean).

**Theorem (Any pattern).** Let $\kappa$ be unramified, $p \geq 7$, $\eta \geq 1$ and $V + 4\eta \leq M$. Let the far windows have width $V$ and start at $b$ at the letters with a property $B$ and at $G$ at the others, with $0 < G \leq b$. If $b < Kp^2$, $2G < Kp$ and $M \leq K$, then $L$ has cup exponent $10^4(K + \lfloor \log_p(2(b + M)) \rfloor)$ for $\mathcal{Q}$.

Lean: `New.Lift.KummerChart.hasCupExponent_any_pattern` (New/Congruences/Lifting/CupOrthogonalityBounds.lean).

**Theorem (Sparse thick letters).** Let $\eta \geq 1$, and let the far windows have width $V$ and start at $b$ at the letters with $B$ and at $G$ at the others, with $G + V \leq \eta$. Let $J \geq 1$. Suppose no three letters with $B$ follow one another along an orbit of Frobenius with both gaps in $[1, J]$. Suppose that either $\kappa$ is unramified with $p \geq 7$ and $10p^J\eta \leq b$, or the sign $\varepsilon$ is constant and $8e \leq p^{J+1}$. If $2e(b + 5\eta) \leq p^{J+1}\delta$ and $20(J + 1 + d)\eta + \lfloor \log_p(2(b + 5\eta)) \rfloor \leq M$, then $L$ has cup exponent $10^3(\delta + (J+1)M)$ for $\mathcal{Q}$.

Lean: `New.Lift.KummerChart.hasCupExponent_sparse_thick` (New/Congruences/Lifting/CupOrthogonalityBounds.lean).

The fourth result, for tame classes, is stated in [Section 5](/chapter/local-loss/#the-defect-at-a-place-above-l), where it is used.

### Letters that read thickness

In the argument each embedding $\gamma$ of $O$ is *thick* (at a b-place, with far window at $b$) or *thin* (with far window at $G$). It also has a sign $\varepsilon_\gamma$. The bounds on cup products need these data at the letters. The next definition says when the letter determines them.

**Definition (Letters read thickness).** Let $\kappa$ be a Kummer chart, $\mathrm{letter} : I \to \mathbb{C}_\ell$, $\mathrm{th}$ a property and $\varepsilon$ a sign on $I$, $Q, h \in \mathbb{N}$, $T$ a property and $s$ a sign on $\mathbb{C}_\ell$. The letters *read thickness* if

1. $ef = [G_\ell : j(\Gamma)]$;
2. $e \leq h$;
3. for each $g \in I$ with $\mathrm{th}(g)$ or $Q < \ell$: $\mathrm{th}(g) \iff T(\mathrm{letter}(g))$;
4. for the same $g$: $\varepsilon_g = s(\mathrm{letter}(g))$;
5. either $\kappa$ is unramified and $\ell \geq 7$, or $\ell \leq Q$ and $s$ is constant;
6. if $\ell \leq Q$: for every $z \in \mathbb{C}_\ell$ and all $a, a' \in [1, \lfloor \log_\ell h^3 \rfloor]$, if $T(z)$ and $T(z^{\ell^a})$, then not $T(z^{\ell^{a + a'}})$.

Lean: `New.Selmer.LettersReadThick` (New/Congruences/LocalLoss/CrystallineCocycles.lean).

For $\ell \leq Q$ only the thick embeddings are read, and condition 6 is the sparseness of thick letters. For $\ell > Q$ every embedding is read and the chart is unramified.

**Lemma (Windows at the letters).** Let $Q, G, b, \delta, \eta, W \in \mathbb{N}$ with $\eta \leq G$ and $\delta + W \leq G$. Suppose that for each $\gamma$ with $\mathrm{th}(\gamma)$ or $Q < \ell$ we have $\mathrm{th}(\gamma) \iff T(\gamma(\zeta))$ and $\varepsilon_\gamma = s(\gamma(\zeta))$. Suppose $U(\gamma)$ fits the windows $(\eta, \varepsilon_\gamma, b_\gamma + \delta, W)$, with $b_\gamma = b$ if $\gamma$ is thick and $b_\gamma = G$ otherwise. Then for each letter $i$ the set $U_i$ fits the windows
$$\big(\eta^*, s(\omega_i), b^*_i + \delta, W\big), \qquad \eta^* = \begin{cases} 2G & \ell \leq Q, \\ \eta & \ell > Q, \end{cases} \qquad b^*_i = \begin{cases} b & T(\omega_i), \\ G & \text{otherwise.}\end{cases}$$

Lean: `New.Selmer.fitsWindows_letterJumps` (New/Congruences/LocalLoss/CrystallineCocycles.lean).

*Proof.* The member $0$ lies in the low window. Let $u \in U(\gamma)$ with $\gamma(\zeta) = \omega_i$. If $\gamma$ is read, that is $\mathrm{th}(\gamma)$ or $Q < \ell$, then its thickness and sign are those of the letter, and the windows of $\gamma$ are the windows of the letter. A low member $|u| \leq \eta$ also lies in $[-2G, 2G]$, as $\eta \leq G$. If $\gamma$ is not read, then $\gamma$ is thin and $\ell \leq Q$. Both of its windows lie in $[-2G, 2G]$: the low window as $\eta \leq G$, and the far window $\pm[G + \delta, G + \delta + W]$ as $\delta + W \leq G$. So $u$ lies in the widened low window. $\square$

### Small primes

**Lemma (The size of $K$).** Let the sizes be crystalline, $e \leq h$, and $2(b + \delta) < h^2 K$. Then
$$20\big(\lfloor \log_\ell h^3 \rfloor + 1 + d\big)(2G) + \lfloor \log_\ell(2(b + \delta + 10G)) \rfloor \leq K.$$

Lean: `New.Selmer.CrystallineSizes.differentBound_mul_add_log_le` (New/Congruences/LocalLoss/CrystallineCocycles.lean).

*Proof.* The bracket is at most $h$. Indeed $\lfloor \log_\ell h^3 \rfloor < m$ by [the logarithm lemma](/decl/New.Selmer.natLog_lt_of_two_mul_log_lt/), since $h^3 \leq 4b$. Also $d \leq v_\ell(e) + 1 \leq \log_2 h + 1 < m$, since $e \leq h \leq 4b$. And $2m + 1 \leq h$ by size condition 2. Similarly the last logarithm is less than $m \leq h \leq hG$. So the left side is at most $40Gh + hG = 41Gh$. By size condition 4, $2b \geq 198 G h^3$, so $h^2 \cdot 41 G h \leq 2b < h^2 K$, and $41Gh < K$. $\square$

**Theorem (Exponent for small primes).** Let $j$ be an open embedding, the letters read thickness for $(\kappa, \mathrm{letter}, \mathrm{th}, \varepsilon, Q, h, T, s)$, the sizes be crystalline, $\ell \leq Q$ and $2(b + \delta) < h^2 K$. Let $L \in \mathrm{InClass}(\top, \bot, U')$. Suppose at each letter $i$ that $U_i$ fits $(2G, -s(\omega_i), b^*_i + \delta, W)$ and $U'_i$ fits $(2G, s(\omega_i), b^*_i + \delta, W)$. Then $L$ has cup exponent
$$10^4 \cdot K \cdot (\lfloor \log_\ell h^3 \rfloor + 1)$$
for $\mathrm{InClass}(\top, \bot, U)$.

Lean: `New.Selmer.LettersReadThick.hasCupExponent_of_le` (New/Congruences/LocalLoss/CrystallineCocycles.lean).

*Proof.* Apply the theorem on sparse thick letters with low radius $2G$, width $W$, thick start $b + \delta$, thin start $G + \delta$, $J = \lfloor \log_\ell h^3 \rfloor$, $M = K$ and depth $2K$. We check its hypotheses.

- $G + \delta + W \leq 2G$, since $\delta + W \leq G$.
- $J \geq 1$, since $\ell \leq Q \leq h \leq h^3$. Also $h^3 < \ell^{J+1}$.
- Sparseness: the Frobenius power $t$ sends a letter $i$ to $i^{\ell^t}$, and $\omega_{i^{\ell^t}} = \omega_i^{\ell^t}$. Condition 6 of reading thickness then forbids three thick letters with gaps in $[1, J]$.
- The alternative. If $\kappa$ is unramified and $\ell \geq 7$: $10\ell^J \cdot 2G \leq 20 h^3 G \leq b + \delta$ by size condition 4. Otherwise $s$ is constant, and $8e \leq 8h \leq h^3 < \ell^{J+1}$.
- Depth: $e \cdot 2(b + \delta + 10G) \leq h \cdot 2(b + \delta + 10G)$, and this is at most $h^3 \cdot 2K < \ell^{J+1} \cdot 2K$, by $2(b + \delta) < h^2 K$ and the previous lemma, which gives $20G \leq K$.
- The bound for $M = K$ is the previous lemma.

The result is the exponent $10^3(2K + (J+1)K)$. Since $J + 1 \geq 2$, this is at most $10^4 K (J + 1)$, and a larger exponent is also a cup exponent. $\square$

### Large primes with large loss

**Theorem (Exponent for large loss).** Let the sizes be crystalline, $\kappa$ unramified, $\ell \geq 7$, $Q < \ell$, and $j$ an open embedding. Let $L \in \mathrm{InClass}(\top, \bot, U')$. Let $T$ be a property and $s$ a sign on the letters, and suppose $U_i$ fits $(\eta, -s_i, b^*_i + \delta, W)$ and $U'_i$ fits $(\eta, s_i, b^*_i + \delta, W)$, with $b^*_i = b$ if $T(i)$ and $G$ otherwise. If $2b < \ell(v + 1)$, $h^3 \leq v$ and $2v < KQ + Q$, then $L$ has cup exponent $10^4 K m$ for $\mathrm{InClass}(\top, \bot, U)$.

Lean: `New.Selmer.CrystallineSizes.hasCupExponent_of_cube_le` (New/Congruences/LocalLoss/CrystallineCocycles.lean).

*Proof.* Apply the theorem for any pattern with $B = T$, $V = W$, $M = W + 4\eta$, starts $b + \delta$ and $G + \delta$. We check its hypotheses. First, $\eta \geq 1$ as $\delta < \eta$, and $0 < G + \delta \leq b + \delta$. From $2v < (K+1)Q$ and $v \geq h^3$ we get $(K + 1) Q > 2h^3$, so $K$ is at least about $h^3/Q$, which is far larger than $W + 4\eta$ by size condition 7. From $2b < \ell(v + 1)$ and $2v < (K + 1)Q$ with $Q < \ell$, we get $b + \delta < K\ell^2$. Since $G \ll b$, also $2(G + \delta) < K\ell$. The result is the exponent $10^4(K + \lfloor \log_\ell(2(b + \delta + W + 4\eta)) \rfloor)$. The logarithm is less than $m$ by the logarithm lemma, as $2(b + \delta + W + 4\eta) \leq 4b$. Since $K \geq 1$, $K + (m - 1) \leq Km$. $\square$

### Large primes with small loss

If $\lambda < h^3$, the lemma on a multiple in the window says that $\ell$ divides no integer in $(b - 30h^3, b + 30h^3]$.

**Lemma (Gap condition for small loss).** Let the sizes be crystalline, $2b < \ell(v + 1)$ and $v < h^3$. Suppose $\ell$ divides no integer in $(b - 30h^3, b + 30h^3]$. If $a = b + \delta$ or $a = G + \delta$, then $\mathrm{NoMult}(\ell, 6(2(v+1) + \eta + W), a)$.

Lean: `New.Selmer.CrystallineSizes.noMultipleNear` (New/Congruences/LocalLoss/CrystallineCocycles.lean).

*Proof.* Put $n = 6(2(v+1) + \eta + W)$. Since $v < h^3$ and $\eta + W \leq h^3/99$, we get $\delta + n < 30h^3$. From $2b < \ell(v + 1) \leq \ell h^3$ and $99 G h^3 \leq b$ we get $\ell > 198 G$, so $9G \leq \ell$. And $\delta + n \leq 13 h^3 \leq G$. So $G + \delta + n < \ell$. Apply [the gap lemma](/decl/New.Selmer.noMultipleNear_of_forall_not_dvd/) with $c = 30h^3$. $\square$

**Theorem (Defect for small loss).** Let the sizes be crystalline, $\kappa$ unramified, $\ell \geq 7$, $f = [G_\ell : j(\Gamma)]$, $j$ an open embedding and $L \in \mathrm{InClass}(\top, \bot, U')$. Let the windows at the letters be as in the theorem for large loss. Suppose $L$ has few low jumps for $(h, \mu, \eta, U, U')$, or $U'(\gamma) \subset [-\eta, 0]$ for every $\gamma$. Let $2b < \ell(v+1)$, $v < h^3$, $2v < KQ + Q$, and $\mathrm{NoMult}(\ell, 6(2(v+1) + \eta + W), b^*_i + \delta)$ at each letter. If $10^5(\mathrm{rank}_O L \cdot Km + \mu v) \leq y$, then
$$\lambda_O\big(\delta_{\mathrm{InClass}(\top, \bot, U)}(L)\big) \leq [G_\ell : j(\Gamma)] \cdot y.$$

Lean: `New.Selmer.normLength_dualDefect_le_of_noMultipleNear` (New/Congruences/LocalLoss/CrystallineCocycles.lean).

*Proof.* Apply the theorem on generic primes with $a = 2(v + 1)$ and $b_i = b^*_i + \delta$. Its hypotheses hold: $\ell \geq 5$; $\eta \geq 1$; $6(a + \eta + W) < b_i$, since $b_i \geq G \geq 99h^3$; and $b_i + W + \eta \leq (\ell - 3) \cdot 2(v + 1)$, since $2\ell(v + 1) > 4b$ while $6(v + 1) + b + \delta + W + \eta \leq 2b$. The gap condition is a hypothesis.

Case 1: $\lfloor h/5 \rfloor \leq v$ and $L$ has few low jumps. Part (b) with the bound $\mu$ gives
$$\lambda_O(\delta) \leq 11 f\big(\mu(2(v+1) + 1) + \mathrm{rank}\,L\,(W + 1)\big),$$
since $\lambda_O(\mathrm{length}(O/\ell)) = 1$. Here $2(v + 1) + 1 \leq 6v$, as $v \geq 1$. Also $W + 1 \leq K$, since $v \geq h/5 - 1$ and $h \geq 99(W + 1)Q$, so $2v/Q > W + 1$. With $m \geq 1$ the right side is at most $f \cdot 10^5(\mathrm{rank}\,L \cdot Km + \mu v) \leq f y$.

Case 2: otherwise. If every $U'(\gamma) \subset [-\eta, 0]$, part (a) gives $\delta = 0$. If not, $L$ has few low jumps and $v < h/5$. Then every negative member $u$ of $U(\gamma)$ or $U'(\gamma)$ has $u \leq -h/2 < -2(v + 1)$. So no member lies in $[-2(v+1), 0)$, and part (a) gives $\delta = 0$. $\square$

### The bound at one place

**Theorem (Crystalline bound).** Let $Q, m, h, \mu$ be given and let $(Q, m, h, G, b, \delta, \eta, W)$ be crystalline sizes. Let $\mathrm{th}$ be a property and $\varepsilon$ a sign on the maps $\gamma : O \to \mathbb{C}_\ell$. Suppose that for each $\gamma$, $U(\gamma)$ fits $(\eta, -\varepsilon_\gamma, b_\gamma + \delta, W)$ and $U'(\gamma)$ fits $(\eta, \varepsilon_\gamma, b_\gamma + \delta, W)$, with $b_\gamma = b$ if $\mathrm{th}(\gamma)$ and $G$ otherwise. Let $L \in \mathrm{InClass}(\top, \bot, U')$. Suppose $L$ has few low jumps for $(h, \mu, \eta, U, U')$, or every $U'(\gamma) \subset [-\eta, 0]$. Put $\lambda = \mathrm{crysLoss}(h, b, \ell)$ and let
$$10^5\big(\mathrm{rank}_O L \cdot \lfloor 2\lambda/Q \rfloor \cdot m + \mu \lambda\big) \leq y.$$
Let $j$ be an open embedding, $\kappa$ a Kummer chart, $\zeta \in O$ with $\zeta^{\ell^f-1} = 1$, and suppose the letters $\gamma \mapsto \gamma(\zeta)$ read thickness for $(\kappa, \mathrm{th}, \varepsilon, Q, h, T, s)$. Then
$$\lambda_O\big(\delta_{\mathrm{InClass}(\top, \bot, U)}(L)\big) \leq [G_\ell : j(\Gamma)] \cdot y.$$

Lean: `New.Selmer.normLength_dualDefect_le_of_crystallineSizes` (New/Congruences/LocalLoss/CrystallineCocycles.lean).

*Proof.* Write $v = \lambda$ and $K = \lfloor 2v/Q \rfloor$, so that $2v < KQ + Q$. The proof uses only three facts on $v$: $2b < \ell(v + 1)$, and $h^3 \leq v$ whenever $\ell$ divides an integer in $(b - 30h^3, b + 30h^3]$; both are from [Section 3](/chapter/local-loss/#the-crystalline-loss-and-the-sizes). By the size conditions, $\eta \leq G$ and $\delta + W \leq G$. The lemma on windows at the letters, applied to $U$ with the sign $-s$ and to $U'$ with $s$, gives the windows at the letters, with low radius $2G$ if $\ell \leq Q$ and $\eta$ otherwise. For $x \leq m$, an exponent $10^4 K x$ satisfies $\mathrm{rank}\,L \cdot 2 \cdot 10^4 K x \leq y$.

Case $\ell \leq Q$. From $2b < \ell(v + 1) \leq Q(v + 1)$, $2v < (K + 1)Q$, $Q^2 \ll h$ and $h + \delta \leq b$ one gets $2(b + \delta) < h^2 K$. The logarithm lemma gives $\lfloor \log_\ell h^3 \rfloor < m$. So the exponent for small primes is $10^4 K x$ with $x = \lfloor \log_\ell h^3 \rfloor + 1 \leq m$. The theorem [exponent to defect](/decl/New.Selmer.normLength_dualDefect_le_of_hasCupExponent/) gives the bound.

Case $\ell > Q$. Condition 5 of reading thickness gives that $\kappa$ is unramified and $\ell \geq 7$. If $h^3 \leq v$, the exponent for large loss is $10^4 K m$, and exponent to defect gives the bound. If $v < h^3$, then $\ell$ divides no integer in $(b - 30h^3, b + 30h^3]$, by the contrapositive of the lemma on a multiple in the window. The gap lemma gives $\mathrm{NoMult}$ at $b + \delta$ and at $G + \delta$. Since $e = 1$, condition 1 gives $f = [G_\ell : j(\Gamma)]$. The theorem for small loss gives the bound. $\square$

**Remark (Formalization).** The quotient $\lfloor 2\lambda/Q \rfloor$ is a quotient of natural numbers, and the bound $10^5(\dots)$ is a natural number cast to the nonnegative reals. The chart $\kappa$, the root $\zeta$ and the functions $T, s$ are inputs of the theorem. [Section 5](/chapter/local-loss/#the-defect-at-a-place-above-l) builds them for large $O$.

**Example (A picture of the regimes).** For the data, $Q = kt$ and $h = h_2 = r^8$. A prime $\ell \leq kt$ is small, and then the defect costs a factor $\lfloor \log_\ell h_2^3 \rfloor + 1 \leq m$ in the exponent. A prime $\ell > kt$ with $\ell$ dividing an integer near $b$ has loss $\lambda \geq h_2^3$, and the bound for any pattern applies. A prime $\ell > kt$ with no multiple near $b$ and $\lambda < h_2^3$ falls in the third regime. There the defect is $0$ unless $L$ has negative jumps near $0$ and $\lambda \geq h_2/5$; this is the model case of the chapter.
