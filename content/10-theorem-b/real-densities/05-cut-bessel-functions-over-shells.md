---
title: Cut Bessel functions over shells
lean:
  - New/Spanning/Frames/RealShells.lean
decls:
  - New.Floors.IsCutBessel.formConst
  - New.Floors.dyadicShell
  - New.Floors.measurableSet_positionBall
  - New.Floors.exists_mem_dyadicShell
  - New.Floors.notMem_positionBall_of_mem_dyadicShell
  - New.Floors.IsCutBessel.mul_pow_four_le_s
  - New.Floors.IsCutBessel.volumeExponent_eq
  - New.Floors.IsCutBessel.max_pow_le_mul_max_one_pow
  - New.Floors.IsCutBessel.headWeight_succ_of_le
  - New.Floors.IsCutBessel.exists_gauge_isHead
  - New.Floors.IsCutBessel.pairingNormSq_le
  - New.Floors.IsCutBessel.formMajorant_eq_zero_of_lt
  - New.Floors.IsCutBessel.floorForm_eq_zero_of_lt
  - New.Floors.IsCutBessel.floorMassLe
  - New.Floors.IsCutBessel.one_le_massBound
  - New.Floors.IsCutBessel.two_mul_div_pow_le_of_pow_le
  - New.Floors.IsCutBessel.isShell_dyadicShell
  - New.Floors.IsCutBessel.formConst_mul_lintegral_le
  - New.Floors.IsCutBessel.formConst_mul_setLIntegral_compl_positionBall_le
  - New.Floors.IsCutBessel.lintegral_formMajorant_ne_top
  - New.Floors.IsCutBessel.shell_bound_le_dampedPower
  - New.Floors.IsCutBessel.pi_sq_div_sq_pow_le
  - New.Floors.IsCutBessel.norm_floorForm_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Cut Bessel functions over shells

This section bounds the forms $\mathcal I_j(p, q; \omega)$ of a cut Bessel function $F$ for $j \leq \varrho$. The general machine of [the chapter on frames](/chapter/local-frames/) bounds such a form by a sum over shells of positions. This section supplies the shells at $\mathbb C$, the mass bound, the size of the pairing and a gauge in which both lists are heads. The result is the bound of the forms by the head weights and the decay $\ell_{k - n^7}$ of [Section 1](/chapter/real-densities/#the-chapter-and-its-place).

### The objects of the general machine

The general machine uses the following objects. Each is stated here in one line. [The chapter on frames](/chapter/local-frames/) gives the details.

1. The head density is $\kappa_j(p, q) = \prod_{a < j} \operatorname{mod}(p_a q_a)^{d_a/2}$ with $d_a = k + 1 + 2(\varrho - a - 1)$ (Lean: `New.Floors.PlaceData.headDensity`, New/Spanning/Frames/Densities.lean).
2. The form is $\mathcal I_j(p, q; \omega) = \kappa_j(p, q) \int \Phi_j(x, g; \omega)\, d(\mathsf M \times \mathsf m_j)$, where $\Phi_j$ is a double integral over floor $j$ of two partial correlations of $F$ (Lean: `New.Floors.PlaceData.floorForm`).
3. The number $\mathsf F_j(x; \omega)$ is the integral over $g$ of $|\Phi_j(x, g; \omega)|$ (Lean: `New.Floors.PlaceData.formIntegrandL1Norm`). The theorem `New.Floors.PlaceData.enorm_floorForm_le` gives $|\mathcal I_j| \leq \kappa_j \int \mathsf F_j\, d\mathsf M$.
4. The majorant $\mathsf F^+_j(x)$ is the same integral with the moduli taken inside (Lean: `New.Floors.PlaceData.formMajorant`). For a cut function and $|\omega| \leq 1$, $\mathsf F_j(x; \omega) \leq \mathsf F^+_j(x)$ (Lean: `New.Floors.PlaceData.IsCut.formIntegrandL1Norm_le_formMajorant`).
5. For a gauge $\Gamma$, the number $P_\Gamma(x)$ is a product of two second moments of the correlations with constants of the gauge (Lean: `New.Floors.Gauge.weightedSquareProduct`). A number $f$ has the gain $\varsigma$ at $x$ if $f^2 \leq \varsigma^2 P_\Gamma(x)$.
6. The pairing $\|F\|_{\mathrm{pair}}^2$ is the double integral of $|\langle F(x), F(y) \rangle|^2$ over $\mathsf U \backslash G_1$ in both variables (Lean: `New.Floors.PlaceData.pairingNormSq`).

### The constant of the forms

**Definition.** The constant of the forms is

$$c_F = \frac{\operatorname{vol} U(k)}{\operatorname{vol} U(r)\, (\lambda\, |I|)^2},$$

where $\lambda$ is the ratio of the two Haar measures of [Section 2](/chapter/real-densities/#haar-measure-and-the-floors).

Lean: `New.Floors.IsCutBessel.formConst` (New/Spanning/Frames/RealShells.lean).

**Remark (Formalization).** The ratio $\lambda$ is an extended real. The source uses its real part `toReal`, which is $0$ for $\lambda = \infty$. Section 2 proves $0 < \lambda < \infty$, so the real part is $\lambda$ and $c_F > 0$.

Two facts on the sizes are used often. They are $10^{10} n^4 \leq s$, and the volume exponent of the place datum at $\mathbb C$ is $s$.

Lean: `New.Floors.IsCutBessel.mul_pow_four_le_s`, `New.Floors.IsCutBessel.volumeExponent_eq` (New/Spanning/Frames/RealShells.lean).

### Dyadic shells

**Definition.** For $i \in \mathbb N$, the dyadic shell $S_i$ is the set of $x \in G_1$ such that $i$ is the least $l$ for which $2^l$ bounds the moduli of all entries of $x - 1$.

Lean: `New.Floors.dyadicShell` (New/Spanning/Frames/RealShells.lean).

**Lemma.** Every $x \in G_1$ lies in some dyadic shell. Each position ball is measurable.

Lean: `New.Floors.exists_mem_dyadicShell`, `New.Floors.measurableSet_positionBall` (New/Spanning/Frames/RealShells.lean).

*Proof.* The entries of $x - 1$ are bounded by its operator norm $B$. Some $2^l$ exceeds $B$, so the set of such $l$ is not empty, and its least element is the index of the shell. The position ball is an intersection of finitely many closed conditions on continuous functions. $\square$

**Lemma.** Let $x \in S_i$, $T \geq 1$ and $2T^{99n} \leq 2^i$. Then $x$ is not in the position ball at scale $T$.

Lean: `New.Floors.notMem_positionBall_of_mem_dyadicShell` (New/Spanning/Frames/RealShells.lean).

*Proof.* Suppose that $x$ is in the ball. If $i = 0$, then $2 T^{99n} \leq 1$, which is false since $T \geq 1$. If $i = l + 1$, then $T^{99n} \leq 2^l$, so $2^l$ bounds the entries of $x - 1$. This contradicts the minimality of $l + 1$. $\square$

**Example.** Let the largest modulus of an entry of $x - 1$ be $5$. Then $5 \leq 2^3$ and $5 > 2^2$, so $x \in S_3$. Take $T = 1$. The hypothesis $2 T^{99n} = 2 \leq 2^3$ holds, so $x$ is outside the ball at scale $1$. This agrees with the definition, since the entry of modulus $5$ exceeds $1^{99n} = 1$.

### A gauge for two heads

The gauges of [Section 3](/chapter/real-densities/#the-gauge-at-the-complex-place) have a scale $L \geq \rho$ and the loss $\Lambda = L^2$. A list $p$ is a head of length $j$ for the gauge of scale $L$ if $|p_0 \cdots p_{l-1}|^{-1} \leq L$ for every $l \leq j$ ([Section 4](/chapter/real-densities/#lengths-and-depth)).

**Lemma.** If $L^K \leq B$ and $L \geq 1$, then $\max(L, x)^K \leq B \max(1, x)^K$. If $|p_0 \cdots p_j| \leq R$, then $\Lambda_{R,K}(j+1, p) = \Lambda_{R,K}(j, p) \max(1, |p_0 \cdots p_j|^{-1})^K$.

Lean: `New.Floors.IsCutBessel.max_pow_le_mul_max_one_pow`, `New.Floors.IsCutBessel.headWeight_succ_of_le` (New/Spanning/Frames/RealShells.lean).

*Proof.* The first claim follows from $\max(L, x) \leq L \max(1, x)$. The second is the definition of the head weight with the last factor written out. $\square$

**Lemma (A gauge for two heads).** Let $F$ be a cut Bessel function, $j, K \in \mathbb N$ and $p, q$ lists. There is $L \geq \rho$ with the following properties.

1. The lists $p$ and $q$ are heads of length $j$ for the gauge of scale $L$.
2. For every $R$ that bounds $|p_0 \cdots p_{l-1}|$ and $|q_0 \cdots q_{l-1}|$ for all $l \leq j$, we have $L^K \leq \rho^K \Lambda_{R,K}(j, p)\, \Lambda_{R,K}(j, q)$.

Lean: `New.Floors.IsCutBessel.exists_gauge_isHead` (New/Spanning/Frames/RealShells.lean).

*Proof.* Use induction on $j$. For $j = 0$ take $L = \rho$. The weights are empty products, so the bound is $\rho^K \leq \rho^K$. For the step, let $L$ serve for $j$, and let $x = p_0 \cdots p_j$ and $y = q_0 \cdots q_j$. Put $L' = \max(L, |x|^{-1}, |y|^{-1})$. Then $p$ and $q$ are heads of length $j + 1$ for $L'$. Let $B = \rho^K \Lambda_{R,K}(j, p) \Lambda_{R,K}(j, q)$. The induction gives $L^K \leq B$. The first lemma, used twice, gives $L'^K \leq B \max(1, |x|^{-1})^K \max(1, |y|^{-1})^K$. Since $|x|, |y| \leq R$, the second lemma turns the right side into $\rho^K \Lambda_{R,K}(j+1, p) \Lambda_{R,K}(j+1, q)$. $\square$

**Remark (Formalization).** The head weight is $0$ when some partial product exceeds $R$. Then the second property says $L^K \leq 0$, and the lemma does not give it. The property is stated only for $R$ that bound all partial products, so it is never used in that case. The main bound below treats that case on its own.

### The pieces of the shell sum

**Lemma.** The pairing of a cut Bessel function satisfies $\|F\|_{\mathrm{pair}}^2 \leq \lambda^2 |I|$.

Lean: `New.Floors.IsCutBessel.pairingNormSq_le` (New/Spanning/Frames/RealShells.lean).

*Proof.* Let $\mu$ be the measure that stands for integration over $\mathsf U \backslash G_1$. The functions $|F|^2$ and $|\langle v, F \rangle|^2$ are invariant under $\mathsf U$, so Section 2 turns their $\mu$-integrals into $\lambda$ times integrals for `New.besselQuotMeasure`. For the cut function these integrals are at most $|I|$ and $|v|^2$, by [the Schur bounds](/chapter/bessel-real-place/#schur-bounds-and-orthonormality). The second bound uses that `rep` is irreducible. So the inner integral over $y$ with $v = F(x)$ is at most $\lambda |F(x)|^2$, and the outer integral of $\lambda |F(x)|^2$ is at most $\lambda \cdot \lambda |I|$. $\square$

**Lemma (Large products kill the form).** Let $j \leq \varrho$, $l \leq j$, and let $|p_0 \cdots p_{l-1}| > \rho^{9n}$ or $|q_0 \cdots q_{l-1}| > \rho^{9n}$. Then $\mathsf F^+_j(x) = 0$ for every $x$. If $|\omega| \leq 1$ everywhere, then $\mathcal I_j(p, q; \omega) = 0$.

Lean: `New.Floors.IsCutBessel.formMajorant_eq_zero_of_lt`, `New.Floors.IsCutBessel.floorForm_eq_zero_of_lt` (New/Spanning/Frames/RealShells.lean).

*Proof.* An active point would bound the partial products of both lists by $\rho^{9n}$. So no point is active, and the general square bound of the majorant holds with the gain $0$. For the form, $\mathsf F_j(x; \omega) \leq \mathsf F^+_j(x) = 0$ for every $x$, so $|\mathcal I_j| \leq \kappa_j \int 0 = 0$. $\square$

**Lemma (Floor mass).** Let $j \leq \varrho$. For every $g$, the floor measure of floor $j$ of the $\sigma$ with $\sigma g$ near at $j + 1$ is at most

$$V = (\pi \rho^{24})^k \rho^{9999n}.$$

The number $V$ is at least $1$.

Lean: `New.Floors.IsCutBessel.floorMassLe`, `New.Floors.IsCutBessel.one_le_massBound` (New/Spanning/Frames/RealShells.lean).

*Proof.* Use the general mass bound of the gauge (Lean: `New.Floors.Gauge.floorMassLe_one`, New/Spanning/Frames/QuadricPlancherel.lean) for the gauge of scale $\rho$. It gives $\Lambda^{99n \cdot 13}$ times a power of the volume of the vectors of size $11$. At $\mathbb C$ this is at most $(\rho^2)^{99n \cdot 13} ((\rho^2)^{12})^{k - 5}$. Then $(\rho^{24})^{k-5} \leq (\pi\rho^{24})^k$ since $\pi \geq 1$, and $2 \cdot 99 \cdot 13\, n \leq 9999n$. Both factors of $V$ are at least $1$. $\square$

**Lemma.** Let $n \neq 0$, $L \geq 2$, $0 < \tau \leq 1$ and $L^{2400n^2} \leq \tau^{400n^2} H$. Then $2 (L^{11n+1}/\tau)^{99n} \leq H$.

Lean: `New.Floors.IsCutBessel.two_mul_div_pow_le_of_pow_le` (New/Spanning/Frames/RealShells.lean).

*Proof.* Multiply by $\tau^{400n^2}$. Since $\tau \leq 1$ and $99n \leq 400n^2$, the left side is at most $\tau^{99n} \cdot L \cdot (L^{11n+1}/\tau)^{99n} = L^{(11n+1)99n + 1}$. The exponent is at most $2400 n^2$, and the hypothesis closes the chain. $\square$

**Example.** Let $n = 1$, $L = 2$ and $\tau = 1$. The hypothesis is $2^{2400} \leq H$. The conclusion is $2 \cdot (2^{12})^{99} = 2^{1189} \leq H$, which follows.

**Theorem (Dyadic shells are shells).** Let $j \leq \varrho$, and let $p$, $q$ be heads of length $j$ for the gauge $\Gamma$ of scale $L \geq \rho$. For every $i$, the dyadic shell $S_i$ is a shell of height $2^i$ for $\Gamma$. That is:

1. $1 \leq 2^i < \infty$;
2. $S_i$ is covered by the positions of size $1$ for at most $2 (2^i)^{9n}$ gauges, each of loss at most $\Lambda (2^i)^2$;
3. if $x \in S_i$, $\sigma < 1$ and $\Lambda^{1200n^2} \leq \sigma^{400n^2} 2^i$, then every point active at $x$ has a frame vector $e_a$, $a \geq j$, of depth at least $\sigma^{-2}$.

Lean: `New.Floors.IsCutBessel.isShell_dyadicShell` (New/Spanning/Frames/RealShells.lean). The notion of a shell is `New.Floors.Gauge.IsShell` (New/Spanning/Frames/Shells.lean).

*Proof.* The first claim is clear. For the cover take the single gauge of scale $L 2^i \geq \rho$. An entry of $x - 1$ for $x \in S_i$ has modulus at most $2^i \leq L 2^i$, so $x$ has size $1$ for this gauge. Its loss is $L^2 (2^i)^2 = \Lambda (2^i)^2$. One gauge is at most $2 (2^i)^{9n}$ gauges. For the third claim, write $\sigma = \tau$ as a real number. Since $\Lambda = L^2$, the hypothesis reads $L^{2400n^2} \leq \tau^{400n^2} 2^i$, and it forces $\tau > 0$. Put $T = L^{11n+1}/\tau$. The previous lemma gives $2T^{99n} \leq 2^i$, and $T \geq L^{11n+1} \geq 1$. So $x$ is outside the position ball at scale $T$. Also $T \geq L^{11n}$ and $T^{-1} = \tau/L^{11n+1} \leq \tau/2$. The corollary [far means deep](/chapter/real-densities/#lengths-and-depth) now gives the deep vector. $\square$

### The sum over the shells

The general sum over shells (Lean: `New.Floors.Gauge.lintegral_le_of_shells`, New/Spanning/Frames/Shells.lean) reads as follows. Let shells $S_i$ of height $2^i$ cover the support of $f \leq \mathsf F^+_j$, let the floor mass be at most $V \geq 1$, let $f$ have the gain $V e^{s}$ at each position when $e < 1$, and let $9 \cdot 10^7 n^4 + r' \leq s$. Then

$$\kappa_j \int f\, d\mathsf M \leq V \min(1, e)^{r'}\, \Lambda^{4 \cdot 10^8 n^4}\, N(F),$$

where $N(F)$ is the product of the floor moduli, of $\operatorname{kernelBound}^{|{\rm Free}| \varrho}$ and of $\|F\|_{\mathrm{pair}}^2$ (Lean: `New.Floors.PlaceData.shellNormalization`).

**Theorem (The shell sum at $\mathbb C$).** Let $j \leq \varrho$, let $p$, $q$ be heads of length $j$ for the gauge of scale $L$, and let $t \geq 1$. Let $0 \leq \varphi \leq \mathsf F^+_j$. If $t > 1$, let $\varphi(x)^2 \leq (V/t^s)^2 P_\Gamma(x)$ for every $x$. Then

$$|I|\; c_F\, \kappa_j \int \varphi\, d\mathsf M \leq \frac{\Theta\, L^{10^9 n^4} \rho^{24k}\, t^{10^8 n^4}}{t^s}.$$

Lean: `New.Floors.IsCutBessel.formConst_mul_lintegral_le` (New/Spanning/Frames/RealShells.lean).

*Proof.* Write $s = 10^8 n^4 + r'$. This is possible since $10^{10} n^4 \leq s$. The dyadic shells cover $G_1$. Use the general sum with $e = t^{-1}$, the floor mass lemma and the dyadic shells. The volume exponent is $s$, and $9 \cdot 10^7 n^4 + r' \leq s$. The sum gives the bound $V t^{-r'} \Lambda^{4 \cdot 10^8 n^4} N(F)$. At $\mathbb C$ the level is $1$ and the kernel bound is $\pi^2$, so $N(F) \leq \pi^{2(k-5)\varrho} \lambda^2 |I|$ by the pairing lemma. With $\Lambda = L^2$, the factors $\lambda^2$, $|I|^2$ and the volumes cancel against $c_F$ and $\Theta$. It remains to show

$$\pi^k \rho^{9999n} L^{8 \cdot 10^8 n^4} \pi^{2(k-5)\varrho} \leq \pi^{(2\varrho+1)k} L^{10^9 n^4}.$$

This holds since $\rho \leq L$ and $9999n + 8 \cdot 10^8 n^4 \leq 10^9 n^4$. $\square$

**Theorem (Remote positions).** Under the same hypotheses on $j$, $p$, $q$, $L$ and $t$, let $C$ be the complement of the position ball at scale $t L^{11n}$. Then

$$c_F\, \kappa_j \int_C \mathsf F^+_j\, d\mathsf M \leq \frac{\Theta\, L^{10^9 n^4} \rho^{24k}\, t^{10^8 n^4}}{t^s}.$$

Lean: `New.Floors.IsCutBessel.formConst_mul_setLIntegral_compl_positionBall_le` (New/Spanning/Frames/RealShells.lean).

*Proof.* Apply the shell sum to $\varphi = \mathsf F^+_j$ on $C$ and $\varphi = 0$ off $C$. Since $|I| \geq 1$, the factor $|I|$ can be dropped. For $t > 1$ and $x \in C$, the corollary on remote positions with $\tau = t^{-1}$ gives a deep vector of depth at least $t^2$. The general bound of a majorant with a deep vector (Lean: `New.Floors.Gauge.formMajorant_sq_le_of_hasDeepVector`, New/Spanning/Frames/Gains.lean) then gives the gain $V t^{-s}$. $\square$

**Corollary.** For $j \leq \varrho$, the integral $\int \mathsf F^+_j\, d\mathsf M$ is finite.

Lean: `New.Floors.IsCutBessel.lintegral_formMajorant_ne_top` (New/Spanning/Frames/RealShells.lean).

*Proof.* Take $L$ from the gauge lemma with $K = 0$ and use the shell sum with $t = 1$. The factor $|I|\, c_F\, \kappa_j$ is not $0$ and not $\infty$. $\square$

**Remark (Formalization).** The form $\mathcal I_j$ is a Bochner integral, which is $0$ for a function that is not integrable. The bounds above hold in that case too, since $|0|$ is at most every bound. The corollary shows that the majorant is integrable, so the junk value does not occur for $|\omega| \leq 1$.

### From the shell sum to the decay

**Lemma.** Let $r > 0$, $L \geq 1$, $H \geq 0$ and $L^{n^6} \leq \rho^{n^6} H$. Put $t = \max(1, \rho^{24} r)$. Then

$$\frac{\Theta\, L^{10^9 n^4} \rho^{24k}\, t^{10^8 n^4}}{t^s} \leq \Theta\, b^{2000n^9}\, \ell_{k - n^7}(r^{-1})\, H.$$

Lean: `New.Floors.IsCutBessel.shell_bound_le_dampedPower` (New/Spanning/Frames/RealShells.lean).

*Proof.* Write $k = n^7 + K$. Since $\varrho \geq 10^8$, we have $10^9 n^4 \leq n^6$, and the sizes give $10^8 n^4 + K + 6 \leq s$. Since $L, t \geq 1$, the left side is at most

$$\Theta\, \rho^{n^6} H\, \rho^{24k}\, t^{-(K+6)} = \Theta\, \bigl(\rho^{n^6} \rho^{24 n^7}\bigr) \Bigl(\frac{\rho^{24}}{t}\Bigr)^K t^{-6}\, H.$$

As $\rho = b^{6n+2}$, the factor $\rho^{n^6} \rho^{24n^7}$ is a power of $b$ with exponent at most $2000 n^9$. Since $t \geq \rho^{24} r$, we have $\rho^{24}/t \leq r^{-1}$. Since $t \geq 1$ and $t \geq r$, we have $t^{-1} \leq \min(1, r^{-1})$. The product $r^{-K} \min(1, r^{-1})^6$ is $\ell_K(r^{-1})$, and $K = k - n^7$. $\square$

**Lemma.** Let $\rho \geq 1$, $r > 0$, $\rho^{24} r \geq 1$ and $s \leq m \leq k$. Then for every $e \in \mathbb N$

$$\Bigl(\frac{\pi^2}{r^2}\Bigr)^m \leq \Bigl(\frac{(\pi\rho^{24})^k \rho^e}{(\rho^{24} r)^s}\Bigr)^2.$$

Lean: `New.Floors.IsCutBessel.pi_sq_div_sq_pow_le` (New/Spanning/Frames/RealShells.lean).

*Proof.* Write $\pi/r = \pi\rho^{24}/(\rho^{24} r)$. The numerator $\pi\rho^{24}$ is at least $1$ and its power $m$ is at most its power $k$. The denominator $\rho^{24} r$ is at least $1$ and its power $m$ is at least its power $s$. The factor $\rho^{2e}$ is at least $1$. $\square$

**Theorem (Bound of the forms).** Let $j \leq \varrho$, $y \in \mathbb C^\times$ and $|\omega| \leq 1$. Suppose that for every gauge $\Gamma$ in which $p$ is a head of length $j$, and for every $x$,

$$\mathsf F_j(x; \omega)^2 \leq \Bigl(\frac{\pi^2}{|y|^2}\Bigr)^{|{\rm Free}|} P_\Gamma(x).$$

Then

$$|I|\, |c_F\, \mathcal I_j(p, q; \omega)| \leq \Theta\, b^{2000n^9}\, \ell_{k - n^7}(|y|^{-1})\, \Lambda_{b^{60n^2}, n^6}(j, p)\, \Lambda_{b^{60n^2}, n^6}(j, q).$$

Lean: `New.Floors.IsCutBessel.norm_floorForm_le` (New/Spanning/Frames/RealShells.lean).

The source states the hypothesis as $(\operatorname{kernelBound}/\operatorname{mod}(y))^{|{\rm Free}|}$. At $\mathbb C$ the kernel bound is $\pi^2$, the modulus of $y$ is $|y|^2$, and $|{\rm Free}| = k - 5$.

*Proof.* Let $R = b^{60n^2}$. Since $n \geq 3$ and $\rho = b^{6n+2}$, we have $\rho^{9n} \leq R$. Suppose that some partial product of $p$ or $q$ of length $l \leq j$ has modulus above $R$. Then it is above $\rho^{9n}$, the form is $0$, and the bound holds. Otherwise take $L$ from the gauge lemma with $K = n^6$, so $L^{n^6} \leq \rho^{n^6} H$ with $H$ the product of the two head weights. Put $t = \max(1, \rho^{24} |y|)$. For $t > 1$ we have $t = \rho^{24} |y|$. The previous lemma with $m = k - 5 \geq s$ turns the hypothesis into the gain $V/t^s$. Then $|\mathcal I_j| \leq \kappa_j \int \mathsf F_j\, d\mathsf M$, the shell sum bounds this with $\varphi = \mathsf F_j \leq \mathsf F^+_j$, and the lemma on the decay finishes the proof. $\square$

**Remark (Formalization).** The docstring of the theorem writes the factor of the hypothesis as $(\pi/\|y\|)^{2(k-5)}$. This is the same number as $(\pi^2/|y|^2)^{k-5}$. The hypothesis is checked in [Section 6](/chapter/real-densities/#band-limits-and-the-local-bounds) with the band limits of the Bessel function.
