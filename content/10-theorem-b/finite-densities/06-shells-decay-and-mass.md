---
title: Shells, decay and mass
lean:
  - New/Spanning/Frames/FiniteShells.lean
decls:
  - New.Floors.PlaceData.idealShell
  - New.Floors.IntegralPlace.IsLargeLatticeData.exists_denominator_ideal
  - New.Floors.IntegralPlace.IsLargeLatticeData.exists_generator_of_mem_idealShell
  - New.Floors.IntegralPlace.IsLargeLatticeData.hasDeepVector_of_mem_idealShell
  - New.Floors.IntegralPlace.IsLargeLatticeData.exists_gauge_idealShell_subset
  - New.Floors.PlaceData.dyadicShell
  - New.Floors.IntegralPlace.IsLargeLatticeData.two_pow_clog_le_two_mul
  - New.Floors.IntegralPlace.IsLargeLatticeData.isShell_dyadicShell
  - New.Floors.IntegralPlace.IsLargeLatticeData.lintegral_shells_le
  - New.Floors.IntegralPlace.IsLargeLatticeData.lintegral_formMajorant_ne_top
  - New.Floors.IntegralPlace.IsLargeLatticeData.exists_unit_common_divisor
  - New.Floors.IntegralPlace.IsLargeLatticeData.exists_unit_formIntegrandL1Norm_sq_le
  - New.Floors.IntegralPlace.IsLargeLatticeData.modulus_le_inv_denomIndex
  - New.Floors.IntegralPlace.IsLargeLatticeData.min_sqrt_genIndex_pow_le
  - New.Floors.IntegralPlace.IsLargeLatticeData.enorm_floorForm_le
  - New.Floors.IntegralPlace.IsLargeLatticeData.modulus_le_inv_of_le_cardQuot
  - New.Floors.IntegralPlace.IsLargeLatticeData.modulus_le_half
  - New.Floors.IntegralPlace.IsLargeLatticeData.modulus_le_volume_nonunits
  - New.Floors.IntegralPlace.IsLargeLatticeData.hasDeepVector_of_notMem_congruenceSubgroup
  - New.Floors.IntegralPlace.IsLargeLatticeData.setLIntegral_compl_congruenceSubgroup_le_pow
  - New.Floors.IntegralPlace.IsLargeLatticeData.setLIntegral_compl_congruenceSubgroup_le
  - New.Floors.IntegralPlace.IsLargeLatticeData.massIntegral_le_main_add_error
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Shells, decay and mass

The sum over the shells of [local frames](/chapter/local-frames/#gains-and-shells) bounds an integral over positions cut into shells of height $2^t$. This section makes the cut at the finite places and draws two consequences: the decay of the form of a floor in its frequency, and the bound of the mass integral by a main term plus an error.

Throughout, $F$ is a large lattice datum with level unit $g$, $n = \varrho + 1$, $k$ is the rank, $[R : J]$ is the index of an ideal (`Ideal.cardQuot`, $0$ if infinite), and $\Lambda$ is the loss of the gauge $\Gamma$.

### The model case

Let $R = \mathbb{Z}_p$. The $\varepsilon \in \mathbb{Z}_p$ that clear the denominators of $g^{-1}(x - 1)$ form an ideal $p^e\mathbb{Z}_p$. Group the positions by the least $2^t \ge p^e$. Each group lies in the integral ball of the gauge of scale $p^{2e}$, and a large $e$ forces a deep vector. Over a semilocal ring there are many ideals of one index, and the ideal zeta value counts them.

### Denominator ideals

**Definition (Ideal shell).** For an ideal $J$ of $R$, the shell $S_J$ is the set of positions $x$ such that the set of $\varepsilon \in R$ with $\varepsilon\,(g^{-1}(x - 1))_{ik} \in R$ for all $i, k$ is the image of $J$ in $A$.

Lean: `New.Floors.PlaceData.idealShell` (New/Spanning/Frames/FiniteShells.lean).

**Lemma (The denominator ideal).** For every $x \in \mathsf{G}$ there are a unit $c$ of $A$ and an ideal $J$ of $R$ with $c \in R$, $[R : J] \ne 0$, $[R : J] = |c|^{-1}$, $J = \{\varepsilon : c^{-1}\varepsilon \in R\}$, and $J$ the set of common denominators in $R$ of the entries of $g^{-1}(x - 1)$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.exists_denominator_ideal` (New/Spanning/Frames/FiniteShells.lean).

*Proof.* Let $D$ list $1$ and the entries of $g^{-1}(x - 1)$. The content lemma (`New.Floors.IntegralPlace.exists_content`, Lib/SiegelWeil/OneVector/FinitePlaceDensity.lean) gives a unit $t$ with: $\varepsilon D_i \in R$ for all $i$ if and only if $t\varepsilon \in R$. The common denominators are exactly these $\varepsilon$, the entry $1$ giving $\varepsilon \in R$. Put $c = t^{-1}$; it is in $R$ as $tc = 1$. The ideal lemma (`New.Floors.IntegralPlace.exists_ideal_cardQuot_eq`) gives $J$ with image $cR$ and index $|c|^{-1} \ne 0$. $\square$

**Corollary (A generator).** If $x \in S_J$, then $J = cR$ for a unit $c \in R$ with $[R : J] = |c|^{-1}$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.exists_generator_of_mem_idealShell` (New/Spanning/Frames/FiniteShells.lean).

*Proof.* The lemma gives $c$ and $J'$; $J$ and $J'$ have the same image in $A$, so $J = J'$. $\square$

**Theorem (A deep ideal shell).** Let $\Gamma = \Gamma_\alpha$, let $p, q$ be heads of length $j \le \varrho$ for $\Gamma$, and let $g^{-1}$ have size $1$ if $j \ne 0$. Let $x \in S_J$, $\sigma < 1$ and

$$\Lambda^{990n^2} \le \sigma^{400n^2}\,[R : J].$$

Then $x$ has a deep vector of depth $\sigma^{-2}$ for $W_Z$: every point $y$ active at $x$ has an index $a \ge j$ with $\delta_a(y, x) \ge \sigma^{-2}$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.hasDeepVector_of_mem_idealShell` (New/Spanning/Frames/FiniteShells.lean).

*Proof.* Take $c$ from the corollary. Multiply the hypothesis by $|c|$; as $|c|\,[R : J] = 1$, this gives $|c|\Lambda^{990n^2} \le \sigma^{400n^2}$. Every common denominator $\varepsilon$ lies in $J = cR$, so $c^{-1}\varepsilon \in R$. These are the hypotheses of the theorem "far means deep" of [depth and heads](/chapter/finite-densities/#depth-and-heads), which gives the index $a$ at each active point $y$. By `New.Floors.PlaceData.hasDeepVector_inv_iff`, this is the deep vector of depth $(\sigma^2)^{-1}$. $\square$

**Theorem (One gauge for one ideal).** Let $\Gamma$ be a gauge and $[R : J] \ne 0$. There is a gauge $\Gamma'$ with $S_J \subseteq$ `Γ'.positionsOfSize` and $\Lambda' \le \Lambda\,[R : J]^2$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.exists_gauge_idealShell_subset` (New/Spanning/Frames/FiniteShells.lean).

*Proof.* If $S_J$ is empty, take $\Gamma' = \Gamma$. Otherwise take $c$ from the corollary for some $x_0 \in S_J$, and let $\Gamma'$ be the gauge of scale $\bar cc$. For $x \in S_J$, $c$ is a common denominator, so $\bar cc\,(g^{-1}(x - 1))_{ik} \in R$: every entry has size $1$ for $\Gamma'$. The loss of $\Gamma'$ is $2/|\bar cc| = 2|c|^{-2} = 2[R : J]^2 \le \Lambda[R : J]^2$, since $\Lambda \ge 2$ (the field `New.Floors.Gauge.two_le_loss`). $\square$

### Dyadic shells

**Definition (Dyadic shell).** For $t \in \mathbb{N}$, the dyadic shell $D_t$ is the union of the $S_J$ over the ideals $J$ with $[R : J] \ne 0$ and $\lceil\log_2[R : J]\rceil = t$ (`Nat.clog 2`).

Lean: `New.Floors.PlaceData.dyadicShell` (New/Spanning/Frames/FiniteShells.lean).

**Lemma.** For $N \ne 0$, $2^{\lceil\log_2N\rceil} \le 2N$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.two_pow_clog_le_two_mul` (New/Spanning/Frames/FiniteShells.lean).

*Proof.* For $N = 1$ both sides are $1$ and $2$. For $N > 1$, $c = \lceil\log_2N\rceil \ge 1$ and $2^{c-1} < N$, so $2^c = 2\cdot 2^{c-1} < 2N$. $\square$

**Theorem (Dyadic shells are shells).** Let $\Gamma = \Gamma_\alpha$, let $p, q$ be heads of length $j \le \varrho$ for $\Gamma$, and let $g^{-1}$ have size $1$ if $j \ne 0$. For every $t$, $D_t$ is a shell of height $2^t$ for $\Gamma$, $j$, $p$, $q$ and $W_Z$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.isShell_dyadicShell` (New/Spanning/Frames/FiniteShells.lean).

*Proof.* Clearly $1 \le 2^t < \infty$. Two fields of [a shell](/chapter/local-frames/#gains-and-shells) remain.

*Few gauges.* By the definition of a large lattice datum ([the lattice datum](/chapter/finite-densities/#the-lattice-datum)), $\zeta_R(m)^n \le 1 + 2^{-n}$ and $m < 9n$. A number whose positive power is at most $1 + 2^{-n}$ is at most $2$, so

$$\zeta_R(m) = \sum_{[R : J] \ne 0}[R : J]^{-m} \le 2.$$

So, with $c = 2^{-tm}$, the set $\mathcal{J}$ of ideals with $[R : J]^{-m} \ge 2^{-tm}$ is finite with $\#\mathcal{J} \le 2/c = 2\cdot 2^{tm}$. Let $\mathcal{S} \subseteq \mathcal{J}$ be the ideals with $[R : J] \le 2^t$. For each ideal $J$ of finite index choose $\Gamma_J$ by the theorem on one gauge for one ideal, and let $\mathcal{G} = \{\Gamma_J : J \in \mathcal{S}\}$. Then

$$\#\mathcal{G} \le \#\mathcal{S} \le 2\,(2^t)^m \le 2\,(2^t)^{9n},$$

as $2^t \ge 1$ and $m \le 9n$. Let $x \in D_t$, so $x \in S_J$ with $\lceil\log_2[R : J]\rceil = t$. Then $[R : J] \le 2^t$, so $[R : J]^{-m} \ge 2^{-tm}$ and $J \in \mathcal{S}$, and $x$ lies in the position ball of $\Gamma_J$. For $J \in \mathcal{S}$ the loss of $\Gamma_J$ is at most $\Lambda[R : J]^2 \le \Lambda(2^t)^2$.

*Far means deep.* Let $x \in D_t$, $\sigma < 1$ and $\Lambda^{1200n^2} \le \sigma^{400n^2}2^t$. Take $J$ as above. The lemma gives $2^t \le 2[R : J]$. Since $2 \le \Lambda$, $1 \le \Lambda$ and $990n^2 + 1 \le 1200n^2$,

$$2\Lambda^{990n^2} \le \Lambda^{990n^2 + 1} \le \Lambda^{1200n^2} \le \sigma^{400n^2}2^t \le 2\,\sigma^{400n^2}[R : J].$$

Cancel the $2$ and apply the theorem on a deep ideal shell. $\square$

### The sum over the shells

**Theorem (Sum over the finite shells).** Let $\Gamma = \Gamma_\alpha$, let $p, q$ be heads of length $j \le \varrho$, let $g^{-1}$ have size $1$ if $j \ne 0$, and let $r + 10^8n^4 \le k$. Let $f : \mathsf{G} \to [0, \infty]$ with $f \le \mathsf{F}^*_j$ (for $p$, $q$, $W_Z$), and suppose that if $e < 1$, then $f(x)^2 \le (e^s)^2\,\mathsf{Q}_j(x)$ at every position $x$, where $s$ is the volume exponent. Then

$$\kappa_j(p, q)\int f\,d\mathsf{M} \le \min(1, e)^r\cdot\mathrm{mr}(Z)\cdot\Lambda^{10^9n^4}.$$

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.lintegral_shells_le` (New/Spanning/Frames/FiniteShells.lean).

*Proof.* Step 1: the exponent. Here $F$ has $m + 1$ further pairs, so $s = \#\iota - 2(2m + 4) - (3n + m + 2)$, and the rank equation $k + 1 = \#\iota + 2(m + 1) + 2$ gives $s = k - 7m - 3n - 13 \ge k - 66n - 13 \ge 9\cdot 10^7n^4 + r$, by $m < 9n$ and $n \ge 1$.

Step 2: the cover. If $f(x) \ne 0$, then $x$ is a position (`New.Floors.IntegralPlace.IsLargeLatticeData.mem_positions_of_formMajorant_ne_zero`), and the lemma on the denominator ideal puts $x$ in some $D_t$.

Step 3: the mass of a floor. In the gauge of scale $1$ the loss is $2$ and every size is $R$, so the lemma on the mass of a floor ([quadrics and Plancherel](/chapter/local-frames/#quadrics-and-plancherel)) gives `FloorMassLe j V 1` with $V = 2^{99\cdot 13n} \ge 1$, and $f$ has the gain $Ve^s$.

Step 4: the unit. As $c_P = 1$, the pairing bound of [the finite Bessel vector](/chapter/finite-densities/#the-finite-bessel-vector) gives $\mathcal{N}(W_Z) \le \mathrm{mr}(Z)$.

Step 5. The sum over the shells, with the shells $D_t$, gives

$$\kappa_j\int f\,d\mathsf{M} \le 2^{99\cdot 13n}\min(1, e)^r\Lambda^{4\cdot 10^8n^4}\mathrm{mr}(Z) \le \min(1, e)^r\,\mathrm{mr}(Z)\,\Lambda^{99\cdot 13n + 4\cdot 10^8n^4},$$

by $2 \le \Lambda$. Since $1 \le \Lambda$ and $99\cdot 13n + 4\cdot 10^8n^4 \le 10^9n^4$, the claim follows. $\square$

**Corollary (The majorant is integrable).** If $j \le \varrho$ and $r + 10^8n^4 \le k$ for some $r$, then $\int\mathsf{F}^*_j\,d\mathsf{M} < \infty$ for all sequences of units $p$, $q$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.lintegral_formMajorant_ne_top` (New/Spanning/Frames/FiniteShells.lean).

*Proof.* If $\mathsf{F}^*_j \ne 0$, the gauge adapted to two heads ([depth and heads](/chapter/finite-densities/#depth-and-heads)) and the theorem with $e = 1$ give a finite bound for $\kappa_j\int\mathsf{F}^*_j$, and $\kappa_j(p, q) \ne 0$. $\square$

### Decay in the frequency

The form of floor $j$ has a weight $\omega$ of one of two kinds. For a free head, $\omega(x) = \psi(\xi\,\langle f_j, xf_j\rangle)$, a character of the diagonal Gram entry of index $j$. For a summed head, $\omega = 1$, $j = i + 1$ and $\xi = g^{-1}(p_i^{-1} - q_i^{-1})$. Plancherel's formula ([quadrics and Plancherel](/chapter/local-frames/#quadrics-and-plancherel)) gives a factor $c_P/|\eta|$ per free coordinate for the character $\psi(\eta\,\cdot)$. On the elements of size $200n^2$ the character only sees $\xi$ modulo $\beta R$, $\beta = \alpha^{200n^2}$, so the gain is measured by a unit $\eta \equiv \xi$.

**Lemma (A common divisor).** For units $\xi$, $\beta$ of $A$ there is a unit $\eta$ with $\xi\eta^{-1} \in R$, $\eta^{-1}\beta \in R$, and $\eta = \xi + c\beta$ for some $c \in R$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.exists_unit_common_divisor` (New/Spanning/Frames/FiniteShells.lean).

*Proof.* The ring $R$ is a valuation pair (`New.IsValuationPair`, [the modulus and the generalised index](/chapter/congruence-subgroups/#the-modulus-and-the-generalised-index)): there is an idempotent $e \in R$ with $\xi = dx$ and $\beta = dy$ for $d = \xi - e(\xi - \beta)$ and some $x, y \in R$. From $e^2 = e$ one gets $ed = e\beta$, so $d = \xi + (e - xe)\beta$, and $d\cdot\xi^{-1}x = 1$. Let $\eta = d$, a unit with inverse $\xi^{-1}x$. Then $\xi\eta^{-1} = x \in R$, $\eta^{-1}\beta = y \in R$, and $c = e - xe \in R$. $\square$

**Theorem (The gain unit).** Let $\Gamma = \Gamma_\alpha$, let $p$ be a head of length $j \le \varrho$, let $g^{-1}$ have size $1$ if $j \ne 0$, and let $p_i^{-1} - q_i^{-1}$ have size $1$ for $i < j$. Let $\omega$, $\xi$ be of one of the two kinds. There are units $\eta$, $w$ with $w \in R$, $\xi w \in R$, $\xi\eta^{-1} \in R$,

$$\mathsf{F}_j(x)^2 \le (c_P/|\eta|)^{\#\mathrm{FreeIndex}}\,\mathsf{Q}_j(x)\ \text{ for every position } x,\qquad \min\bigl(1, \sqrt{\mathrm{gi}(\eta)}\bigr)^2 \le |w|\,|\beta^{-1}|,$$

with $\beta = \alpha^{200n^2}$ and $\mathsf{F}_j$ the $L^1$ norm of the integrand with weight $\omega$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.exists_unit_formIntegrandL1Norm_sq_le` (New/Spanning/Frames/FiniteShells.lean).

*Proof.* Free head. Take $\eta = \xi + c\beta$ from the lemma, and $w = \eta^{-1}\beta$. If $z$ has size $200n^2$, then $\beta z \in R$, so $\psi(c\beta z) = 1$ by self duality, and $\psi(\xi z) = \psi(\eta z)$. The bound for a frequency of [gains and shells](/chapter/local-frames/#gains-and-shells) (`New.Floors.Gauge.formIntegrandL1Norm_sq_le_of_char`) needs exactly this agreement, and gives the first bound. Here $w \in R$, $\xi w = (\xi\eta^{-1})\beta \in R$, and $|w||\beta^{-1}| = |\eta|^{-1} = \mathrm{gi}(\eta)$, which is at least $\min(1, \sqrt{\mathrm{gi}(\eta)})^2$.

Summed head. Take $\eta = \xi$ and $w = \beta$. As a product of two elements of size $1$, $\xi$ has size $2 \le 200n^2$, so $\beta\xi \in R$. The bound for two heads (`New.Floors.Gauge.formIntegrandL1Norm_sq_le_of_heads`) gives the first bound. The second holds as $|\beta||\beta^{-1}| = 1$. $\square$

**Lemma (Modulus and denominator).** If $w \in R$ and $\xi w \in R$, then $|w| \le \mathrm{di}(\xi)^{-1}$, where $\mathrm{di}(\xi) = [R : R \cap \xi^{-1}R]$ (`New.denomIndex`).

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.modulus_le_inv_denomIndex` (New/Spanning/Frames/FiniteShells.lean).

*Proof.* The set $R \cap \xi^{-1}R$ is an open subgroup of the compact group $R$, of volume $\mathrm{di}(\xi)^{-1}$. It contains $wR$, since $\xi wa \in R$ for $a \in R$. So $|w| = \mathrm{vol}(wR) \le \mathrm{di}(\xi)^{-1}$ (`New.Floors.IntegralPlace.modulus_le_volume`). $\square$

**Lemma (Trading the gain).** Let $w$, $\xi w$, $\xi\eta^{-1} \in R$, $e = \sqrt{\mathrm{gi}(\eta)}$, and $\min(1, e)^2 \le |w|L$. Then

$$\min(1, e)^{t + 12} \le \sqrt{\mathrm{gi}(\xi)}^{\,t}\,\bigl(\mathrm{di}(\xi)^{-1}L\bigr)^6.$$

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.min_sqrt_genIndex_pow_le` (New/Spanning/Frames/FiniteShells.lean).

*Proof.* As $\xi\eta^{-1} \in R$, $\mathrm{gi}(\xi\eta^{-1}) \ge 1$ and $\mathrm{gi}(\eta) \le \mathrm{gi}(\xi\eta^{-1})\mathrm{gi}(\eta) = \mathrm{gi}(\xi)$. Write $\min(1, e)^{t+12} = \min(1, e)^t(\min(1, e)^2)^6$. Bound the first factor by $e^t \le \sqrt{\mathrm{gi}(\xi)}^t$ and the second by $(|w|L)^6 \le (\mathrm{di}(\xi)^{-1}L)^6$. $\square$

**Theorem (Decay of the form of a floor).** Let $Z$ be an intermediate group, $j \le \varrho$, $t + 10^{10}n^4 \le k$ and $10^{10}n^4 \le L$, and let $\omega$, $\xi$ be of one of the two kinds. Then

$$\|\mathcal{I}_j(p, q, W_Z, \omega)\| \le \mathrm{mr}(Z)\cdot\sqrt{\mathrm{gi}(\xi)}^{\,t}\,\mathrm{di}(\xi)^{-6}\Bigl(\frac{2}{|g|}\Bigr)^L\mathrm{hw}_L(j, p)\,\mathrm{hw}_L(j, q).$$

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.enorm_floorForm_le` (New/Spanning/Frames/FiniteShells.lean).

*Proof.* The norm of the form is at most $\kappa_j\int\mathsf{F}_j\,d\mathsf{M}$, and $\mathsf{F}_j \le \mathsf{F}^*_j$ (`New.Floors.PlaceData.enorm_floorForm_le`, [local frames](/chapter/local-frames/#densities-as-integrals-over-two-frames)). If $\mathsf{F}^*_j = 0$, this bound is $0$.

Otherwise the theorem on a gauge adapted to two heads gives $\alpha$ with $p, q$ heads, $g^{-1}$ of size $1$ if $j \ne 0$, $p_i^{-1} - q_i^{-1}$ of size $1$ for $i < j$, and $\Lambda^E \le (2/|g|)^L\mathrm{hw}_L(j, p)\mathrm{hw}_L(j, q)$ whenever $4E \le L$. The theorem on the gain unit gives $\eta$, $w$. Put $e = \sqrt{\mathrm{gi}(\eta)}$. As $c_P = 1$, $c_P/|\eta| = \mathrm{gi}(\eta) = e^2$ (`New.Floors.IntegralPlace.inv_modulus_eq_sqrt_genIndex_sq`), and if $e < 1$, then $e^{2\#\mathrm{FreeIndex}} \le e^{2s}$ as $s \le \#\mathrm{FreeIndex}$. So $\mathsf{F}_j$ has the gain $e^s$. The sum over the finite shells with $r = t + 12$ (note $t + 12 + 10^8n^4 \le k$) gives

$$\|\mathcal{I}_j\| \le \min(1, e)^{t+12}\,\mathrm{mr}(Z)\,\Lambda^{10^9n^4}.$$

Since $\beta\beta^{-1} = 1 \in R$, $|\beta^{-1}| \le \Lambda^{200n^2}$ (`New.Floors.Gauge.modulus_le`). The lemma on trading the gain, with $L' = \Lambda^{200n^2}$, gives $\min(1, e)^{t+12} \le \sqrt{\mathrm{gi}(\xi)}^t\,\mathrm{di}(\xi)^{-6}\Lambda^{1200n^2}$. So the power of $\Lambda$ is $E = 1200n^2 + 10^9n^4$, and $4E \le 4800n^4 + 4\cdot 10^9n^4 \le 10^{10}n^4 \le L$. The bound on $\Lambda^E$ concludes. $\square$

**Remark (Formalization).** First, `New.denomIndex` is a relative index, set to $0$ when the index is infinite, and then $\mathrm{di}(\xi)^{-1} = \infty$. For a unit $\xi$ the index is finite (an open subgroup of the compact $R$), so the junk value does not occur. Second, $\mathrm{gi}(\xi) = |\xi|^{-1}$, so $\sqrt{\mathrm{gi}(\xi)}^t$ is a gain only when $|\xi| > 1$. Third, the constants $r + 10^8n^4 \le k$ and $t + 10^{10}n^4 \le k$ (line 59) are not checked here against the rank that later chapters choose (finding F-091, question Q-26).

### The mass integral

**Lemma (Small moduli).** Let $c \in R$ be a unit of $A$ with $c^{-1} \notin R$. If $Q \le [R : I]$ for every proper ideal $I$ of finite index, then $|c| \le Q^{-1}$. In all cases $|c| \le 1/2$, and $|c|$ is at most the volume of the set of non-units of $R$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.modulus_le_inv_of_le_cardQuot`, `New.Floors.IntegralPlace.IsLargeLatticeData.modulus_le_half`, `New.Floors.IntegralPlace.IsLargeLatticeData.modulus_le_volume_nonunits` (New/Spanning/Frames/FiniteShells.lean).

*Proof.* The ideal lemma gives $I$ with image $cR$ and $[R : I] = |c|^{-1}$; $I \ne R$ as $c^{-1} \notin R$. A proper ideal of finite index has index at least $2$, which gives $|c| \le 1/2$. For the last claim, $ca$ is not a unit of $R$ for $a \in R$, as otherwise $c^{-1} = a(ca)^{-1} \in R$; so $cR$ lies in the non-units. $\square$

**Theorem (Off the congruence subgroup there is a deep vector).** Let $e$ bound $|c|$ for every unit $c \in R$ with $c^{-1} \notin R$. If $x \notin K(g)$, then $x$ has a deep vector of depth $e^{-1}$ for $j = 0$, heads $1$, $1$ and $W_Z$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.hasDeepVector_of_notMem_congruenceSubgroup` (New/Spanning/Frames/FiniteShells.lean).

*Proof.* Suppose an active point $y$ has $\mathrm{vol}(\mathfrak{d}_a(y, x)) > e$ for all $a$. For each $a$, [depth and heads](/chapter/finite-densities/#depth-and-heads) gives a unit $c \in \mathfrak{d}_a$, $c \in R$, with $\mathrm{vol}(\mathfrak{d}_a) \le |c|$. If $c^{-1} \notin R$, then $|c| \le e$, which is false; so $c^{-1} \in R$, that is, $c^{-1}$ has size $1$ in the gauge of scale $1$. The lemma that bounded depths bound the position ([depth](/chapter/local-frames/#depth)) then gives that $g^{-1}(x - 1)$ has size $99n$ in this gauge, and every size of this gauge is $R$. So $g^{-1}(x - 1)$ is integral. As $g \in R$ and the split Gram matrix is unimodular, $x \in K(g)$, which is false. $\square$

**Theorem (The complement of the congruence subgroup).** Let $Q \ge 2$ be such that $|c| \le Q^{-1}$ for every unit $c \in R$ with $c^{-1} \notin R$. If $t + 2\cdot 10^9n^4 \le k$, then

$$\int_{\mathsf{G}\setminus K(g)}\mathsf{F}^*_0(1, 1, W_Z)\,d\mathsf{M} \le Q^{-t}\,\mathrm{mr}(Z).$$

For a general bound $e$ in place of $Q^{-1}$ and $r + 10^8n^4 \le k$, the integral is at most $\min(1, e)^r\,\mathrm{mr}(Z)\,2^{10^9n^4}$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.setLIntegral_compl_congruenceSubgroup_le`, `New.Floors.IntegralPlace.IsLargeLatticeData.setLIntegral_compl_congruenceSubgroup_le_pow` (New/Spanning/Frames/FiniteShells.lean).

*Proof.* Take the gauge of scale $1$, where $\Lambda = 2$ and $1$ is a head of length $0$. Let $f$ be $\mathsf{F}^*_0$ off $K(g)$ and $0$ on $K(g)$. At a position off $K(g)$ the last theorem gives a deep vector of depth $e^{-1}$, and the gain from a deep vector (`New.Floors.Gauge.formMajorant_zero_sq_le_of_hasDeepVector`) gives $f^2 \le (e^s)^2\mathsf{Q}_0$. The sum over the finite shells, with $\kappa_0 = 1$, gives the second bound. For the first, take $e = Q^{-1}$ and $r = t + N$ with $N = 10^9n^4$:

$$\min(1, Q^{-1})^{t+N}\,\mathrm{mr}(Z)\,2^N \le Q^{-t}\,\mathrm{mr}(Z)\,(2Q^{-1})^N \le Q^{-t}\,\mathrm{mr}(Z),$$

as $2Q^{-1} \le 1$. $\square$

**Theorem (Main term plus error).** Let $Q \ge 2$ be as in the last theorem and $t + 2\cdot 10^9n^4 \le k$. Then

$$\varkappa(Z) \le \mathsf{M}(Z)\,\mathsf{M}(K(g))\,\bigl(\mathsf{M}(Z) + Q^{-t}\bigr).$$

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.massIntegral_le_main_add_error` (New/Spanning/Frames/FiniteShells.lean).

*Proof.* Split $\varkappa(Z) = \int_{\mathsf{G}}|\int_Z\chi_g(yxy^{-1})\,dy|^2\,dx$ into $K(g)$ and its complement. On $K(g)$ the integral is $\mathsf{M}(Z)^2\mathsf{M}(K(g))$ by [the finite Bessel vector](/chapter/finite-densities/#the-finite-bessel-vector). Off $K(g)$, the pairing in one variable writes the inner integral as $\mathrm{fl}$ times a correlation of $W_Z$, the correlation is at most its pivot integral (`New.Floors.PlaceData.IsPairingKernel.enorm_partialCorrelation_le`), and the square of the pivot integral is $\mathsf{F}^*_0(x)$ (`New.Floors.PlaceData.formMajorant_zero_eq`). So the integrand is at most $\mathsf{F}^*_0(x)\,\mathrm{fl}^2$, and the last theorem bounds the complement by $Q^{-t}\,\mathrm{mr}(Z)\,\mathrm{fl}^2$. Finally $\mathrm{mr}(Z)\,\mathrm{fl}^2 = \mathsf{M}(Z)\,\mathsf{M}(K(g))$ by the definition of the mass ratio. $\square$

[The main term](/chapter/main-term/) applies this theorem with $Z = K$ and $Q = 2$ (New/Spanning/MainTerm/FiniteSieveSystem.lean).
