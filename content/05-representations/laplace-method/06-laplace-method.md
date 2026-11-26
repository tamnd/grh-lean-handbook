---
title: Laplace's method
lean:
  - New/Appendix/DiscreteSeries/Periods.lean
decls:
  - New.DiscreteSeries.norm_mul_sub_mul_le
  - New.DiscreteSeries.norm_le_two_mul_re_add
  - New.DiscreteSeries.inv_one_add_sq_pow_le_exp_pow_four
  - New.DiscreteSeries.le_pow_mul_of_le
  - New.DiscreteSeries.IsLaplaceDatum.norm_laplaceIntegrand
  - New.DiscreteSeries.IsLaplaceDatum.norm_laplaceIntegrand_le_of_far
  - New.DiscreteSeries.norm_coe_sum_eq_max
  - New.DiscreteSeries.isProperMap_sum
  - New.DiscreteSeries.IsLaplaceDatum.one_div_four_le_norm_laplaceIntegrand
  - New.DiscreteSeries.IsLaplaceDatum.norm_laplaceIntegrand_le_mul_re_add_of_near
  - New.DiscreteSeries.IsLaplaceDatum.norm_laplaceIntegrand_le_mul_re_add
  - New.DiscreteSeries.IsLaplaceDatum.norm_laplaceIntegrand_le_pow
  - New.DiscreteSeries.norm_le_two_mul_re_add_mul
  - New.DiscreteSeries.IsLaplaceDatum.norm_laplaceIntegrand_le_two_mul_re_add_mul_pow
  - New.DiscreteSeries.IsLaplaceDatum.norm_laplaceIntegrand_le_two_mul_re_add
  - New.DiscreteSeries.measureReal_div_four_le
  - New.DiscreteSeries.norm_le_add_one_of_norm_sub_one_le
  - New.DiscreteSeries.measure_large_ball_le_pow_mul_small_ball
  - New.DiscreteSeries.IsLaplaceDatum.laplace_method
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Laplace's method

This section proves the theorem of Laplace's method stated in [the opening section](/chapter/laplace-method/). The classical method estimates $\int e^{t f(x)}\,dx$ for large $t$ by the contribution of a neighbourhood of the maximum of $f$ (de Bruijn, *Asymptotic Methods in Analysis*, Chapter 4; Olver, *Asymptotics and Special Functions*, Chapter 3). Here there is no asymptotic expansion. We only need a lower bound, and the argument has two parts. First, the values of $\theta$ lie in a cone about the positive real axis, up to a small error. So there is no cancellation in $\int\theta$. Second, $|\theta| \geq 1/4$ on a small ball, and a covering argument compares the small ball with a large one.

Throughout, $(l, k, j, \tau, B, e, \varphi)$ is a Laplace datum with $B \geq 1$. Both $l$ and $k$ have large gap $h$ and entries bounded by $L$. Write $N = (\#n + \#m)^2$ and assume $\#n + \#m + L \leq \beta$. Put $T = N\log\beta$.

### Two inequalities for complex numbers

**Lemma (Product of two near numbers).** Let $a, c, t \in [0, 1]$. If $|u - a| \leq a/10 + t$ and $|v - c| \leq c/10 + t$, then $|uv - ac| \leq 0.21\,ac + 4t$.
Lean: `New.DiscreteSeries.norm_mul_sub_mul_le` (New/Appendix/DiscreteSeries/Periods.lean).

*Proof.* Write $uv - ac = a(v - c) + (u - a)c + (u - a)(v - c)$ and use $a, c, t \leq 1$. $\square$

**Lemma (Cone).** If $p \geq 0$ and $|z - p| \leq 0.21\,p + 4t$, then $|z| \leq 2\operatorname{Re}z + 12t$.
Lean: `New.DiscreteSeries.norm_le_two_mul_re_add` (New/Appendix/DiscreteSeries/Periods.lean).

*Proof.* We have $|z| \leq p + |z - p|$ and $\operatorname{Re}z \geq p - |z - p|$. So $|z| - 2\operatorname{Re}z \leq 3|z - p| - p \leq 12t$. $\square$

The cone $|z| \leq 2\operatorname{Re}z$ is the set of $z$ with argument at most $\pi/3$. A function $f$ with values in it satisfies $\int|f| \leq 2\operatorname{Re}\int f \leq 2|\int f|$. This is the whole point of the phase removal.

### Far from the compact subgroups

**Lemma (Modulus).** $|\theta(s)| = |c_l(g)|\,|c_k(g')|$.
Lean: `New.DiscreteSeries.IsLaplaceDatum.norm_laplaceIntegrand` (New/Appendix/DiscreteSeries/Periods.lean).

*Proof.* $\varphi(s)$ is imaginary, so $|e^{-\varphi(s)}| = 1$. $\square$

**Lemma (A logarithmic inequality).** Let $T \geq 1$, $T\rho = 10^{-13}$ and $h \geq 10^{30}T^3$. Then $(1 + \rho^2)^{-h} \leq e^{-400T}$.
Lean: `New.DiscreteSeries.inv_one_add_sq_pow_le_exp_pow_four` (New/Appendix/DiscreteSeries/Periods.lean).

*Proof.* Use $\log(1 + x) \geq 2x/(x + 2)$ for $x = \rho^2$. Then $h\log(1 + \rho^2) \geq 10^{30}T^3 \cdot \rho^2 \cdot (2/(\rho^2 + 2)) \geq 400T$, since $T^2\rho^2 = 10^{-26}$ and $\rho \leq 1/100$. $\square$

**Lemma (Far points).** Let $T \geq 1$, $T\rho = 10^{-13}$ and $h \geq 10^{30}T^3$. If $\|y\|^2 + \|y'\|^2 \geq \rho^2$ (Frobenius norm), then $|\theta(s)| \leq e^{-100T}$.
Lean: `New.DiscreteSeries.IsLaplaceDatum.norm_laplaceIntegrand_le_of_far` (New/Appendix/DiscreteSeries/Periods.lean).

*Proof.* By [the decay theorem](/decl/New.DiscreteSeries.norm_dsCoeff_pow_four_le/) for $l$ and for $k$,
$$ |\theta(s)|^4 \leq (1 + \|y\|^2)^{-h}(1 + \|y'\|^2)^{-h} \leq (1 + \rho^2)^{-h}, $$
since $(1 + \|y\|^2)(1 + \|y'\|^2) \geq 1 + \|y\|^2 + \|y'\|^2$. Apply the previous lemma. $\square$

### The cone near the identity

**Lemma (Near points).** Let $\log\beta \geq 1$ and $\delta T \leq 10^{-12}$. If $\|g - 1\| \leq \delta$ and $\|g' - 1\| \leq \delta$ (Frobenius norm), then
$$ |\theta(s)| \leq 2\operatorname{Re}\theta(s) + 12e^{-100T}. $$
Lean: `New.DiscreteSeries.IsLaplaceDatum.norm_laplaceIntegrand_le_mul_re_add_of_near` (New/Appendix/DiscreteSeries/Periods.lean).

*Proof.* Write $\overline{c_k(g')} = c_{-k}(g')$ by the conjugation formula, and note that the lowest $K$-type of $-k$ has weight $-\mu'$. Since $\delta \leq 1/2$, the phase is still $\varphi(s)$ when $g - 1$ and $g' - 1$ are replaced by $\log g$ and $\log g'$. The source proves this from the additivity of $\varphi$ and the power series of the logarithm.
Lean: `New.DiscreteSeries.IsLaplaceDatum.phase_logOneAdd` (New/Appendix/DiscreteSeries/Localization.lean).

So
$$ \theta(s) = \frac{c_l(g)}{\exp\operatorname{tr}(\mu\log g)}\cdot\frac{c_{-k}(g')}{\exp\operatorname{tr}(-\mu'\log g')}. $$
The hypotheses of [the Gaussian shape](/decl/New.DiscreteSeries.exists_norm_dsCoeff_div_cexp_sub_le/) hold with this $T$, since $\#n^2 \leq T$ and $\#n^2\log(\#n + L + 1) \leq T$, and the same for $m$. So the two factors are within $a/10 + e^{-100T}$ of some $a \in [0, 1]$ and within $c/10 + e^{-100T}$ of some $c \in [0, 1]$. The two lemmas on complex numbers give the cone. $\square$

**Theorem (Cone).** Let $\log\beta \geq 1$ and $h \geq 10^{30}T^3$. Then for every $s \in S$,
$$ |\theta(s)| \leq 2\operatorname{Re}\theta(s) + 12e^{-100T}. $$
Lean: `New.DiscreteSeries.IsLaplaceDatum.norm_laplaceIntegrand_le_mul_re_add` (New/Appendix/DiscreteSeries/Periods.lean).

*Proof.* Let $\rho = 10^{-13}/T$. If $\|y\|^2 + \|y'\|^2 \leq \rho^2$, then [the localization theorem](/decl/New.DiscreteSeries.IsLaplaceDatum.exists_laplaceIntegrand_eq_and_norm_subOnePair_le/) gives $t$ with $\theta(t) = \theta(s)$ and both components within $4\rho$ of $1$. Since $4\rho T \leq 10^{-12}$, the lemma on near points applies at $t$. Otherwise the lemma on far points gives $|\theta(s)| \leq e^{-100T}$, and then $|\theta(s)| - 2\operatorname{Re}\theta(s) \leq 3|\theta(s)| \leq 12e^{-100T}$. $\square$

This is the only place where the localization of section 3 is used. Without it, the Gaussian shape would only control $\theta$ in a ball about $1$, while $\theta$ is not small on the whole compact part.

### Decay with the operator norm

From here on, $\|\cdot\|$ is the operator norm, and $g \oplus g'$ is the block diagonal matrix in $U(\varepsilon \oplus \eta)$. Then $\|g \oplus g'\| = \max(\|g\|, \|g'\|)$, and $s \mapsto g \oplus g'$ is proper if $s \mapsto g$ is proper and $s \mapsto g'$ is continuous.
Lean: `New.DiscreteSeries.norm_coe_sum_eq_max` (New/Appendix/DiscreteSeries/Periods.lean), `New.DiscreteSeries.isProperMap_sum` (New/Appendix/DiscreteSeries/Periods.lean).

**Lemma (Decay of the integrand).** For $c \leq h$, $|\theta(s)| \leq (2/\|g \oplus g'\|)^c$.
Lean: `New.DiscreteSeries.IsLaplaceDatum.norm_laplaceIntegrand_le_pow` (New/Appendix/DiscreteSeries/Periods.lean).

*Proof.* Apply [the operator norm decay](/decl/New.DiscreteSeries.norm_dsCoeff_le_pow/) of the previous chapter to the component of larger norm, and bound the other coefficient by $1$. $\square$

**Lemma (Geometric mean).** If $|z| \leq 2\operatorname{Re}z + 12E^2$ and $|z| \leq G^2$ with $E, G \geq 0$, then $|z| \leq 2\operatorname{Re}z + 6EG$.
Lean: `New.DiscreteSeries.norm_le_two_mul_re_add_mul` (New/Appendix/DiscreteSeries/Periods.lean).

*Proof.* The quantity $|z| - 2\operatorname{Re}z$ is at most $12E^2$ and at most $3|z| \leq 3G^2$. So it is at most $\sqrt{12E^2\cdot 3G^2} = 6EG$. $\square$

**Lemma (Cone with a decaying error).** Let $\log\beta \geq 1$ and $h \geq 10^{30}T^3$. Then
$$ |\theta(s)| \leq 2\operatorname{Re}\theta(s) + 6\beta^{-50N}\left(\frac{2}{\|g \oplus g'\|}\right)^{9N}. $$
Lean: `New.DiscreteSeries.IsLaplaceDatum.norm_laplaceIntegrand_le_two_mul_re_add_mul_pow` (New/Appendix/DiscreteSeries/Periods.lean).

*Proof.* Take $E^2 = e^{-100T} = \beta^{-100N}$ and $G^2 = (2/\|g \oplus g'\|)^{18N}$. The decay lemma applies with $c = 18N$, since $18N \leq h$. $\square$

**Lemma (The pointwise bounds).** Let $\beta \geq 3$ and $h \geq 10^{30}T^3$. Put $G(s) = (2/\|g\oplus g'\|)^{9N}$. Then $|\theta(s)| \leq G(s)$ and $|\theta(s)| \leq 2\operatorname{Re}\theta(s) + 6\beta^{-50N}G(s)$.
Lean: `New.DiscreteSeries.IsLaplaceDatum.norm_laplaceIntegrand_le_two_mul_re_add` (New/Appendix/DiscreteSeries/Periods.lean).

*Proof.* The second bound is the previous lemma, since $\beta \geq 3$ gives $\log\beta \geq 1$. The first is the decay lemma with $c = 9N$. $\square$

### The small ball

**Lemma (Lower bound on a small ball).** Let $\#n + \#m + L \leq \beta$. If $\|g \oplus g' - 1\| \leq (200\beta^5)^{-1}$, then $|\theta(s)| \geq 1/4$.
Lean: `New.DiscreteSeries.IsLaplaceDatum.one_div_four_le_norm_laplaceIntegrand` (New/Appendix/DiscreteSeries/Periods.lean).

*Proof.* Both $\|g - 1\|$ and $\|g' - 1\|$ are at most $(200\beta^5)^{-1}$, and $\#n + L + 1 \leq \beta$. By [the lower bound near one](/decl/New.half_le_norm_dsCoeff/), both coefficients have modulus at least $1/2$. $\square$

**Lemma (Integration).** Let $|f| \leq 2\operatorname{Re}f + cG$ everywhere, with $f$ and $G$ integrable, and $|f| \geq 1/4$ on a set $A$. Then $\nu(A)/4 \leq 2|\int f| + c\int G$.
Lean: `New.DiscreteSeries.measureReal_div_four_le` (New/Appendix/DiscreteSeries/Periods.lean).

*Proof.* $\nu(A)/4 \leq \int_A|f| \leq \int|f| \leq 2\operatorname{Re}\int f + c\int G$. $\square$

### The covering

Let $\nu$ be a right invariant measure on $S$. For a homomorphism $J$ from $S$ to a unitary group of size $d$, and $\beta \geq 10^{12}$, the previous chapter gives a covering bound. With radii $1/(200\beta^5)$ and $\beta + 1$, it reads
$$ \nu\{\|J(s)\| \leq \beta + 1\} \leq \beta^{16 d^2}\,\nu\{\|J(s) - 1\| \leq (200\beta^5)^{-1}\}. $$
Lean: `New.DiscreteSeries.measure_large_ball_le_pow_mul_small_ball` (New/Appendix/DiscreteSeries/Periods.lean).

The proof takes a maximal separated family in the large set; the right translates of the small ball by its points cover the large set, and a packing bound counts the family. The constant is $K^{2d^2}$ with $K = \beta^8 \geq 3\cdot 200\beta^5(\beta + 1)^2$. The general statement is [the covering bound](/decl/New.DiscreteSeries.measure_ball_le_covering/). The same chapter shows that $\int(2/\|J(s)\|)^c\,d\nu \leq 16^c\,\nu\{\|J(s) - 1\| \leq 1\}$ for $c > 8d^2$ and $J$ proper; see [the decay integral](/decl/New.DiscreteSeries.integral_decay_le/).

**Lemma (Unit ball).** If $\|A - 1\| \leq 1$ and $r \geq 1$, then $\|A\| \leq r + 1$.
Lean: `New.DiscreteSeries.norm_le_add_one_of_norm_sub_one_le` (New/Appendix/DiscreteSeries/Periods.lean).

**Lemma (Absorbing the error).** Let $\beta \geq 16$, $N \geq 1$ and $V, I \geq 0$. If $V \leq \beta^{16N}W$ and $W/4 \leq 2I + 6\beta^{-50N}16^{9N}V$, then $V \leq \beta^{20N}I$.
Lean: `New.DiscreteSeries.le_pow_mul_of_le` (New/Appendix/DiscreteSeries/Periods.lean).

*Proof.* We get $V \leq 8\beta^{16N}I + 24\beta^{16N}\beta^{-50N}16^{9N}V$. Since $16 \leq \beta$, we have $48\beta^{16N}16^{9N} \leq \beta^{2}\beta^{16N}\beta^{9N} \leq \beta^{50N}$. So the coefficient of $V$ on the right is at most $1/2$. So $V \leq 16\beta^{16N}I \leq \beta^{20N}I$. $\square$

### The theorem

We now prove the theorem of Laplace's method, in the form of [the opening section](/chapter/laplace-method/).
Lean: `New.DiscreteSeries.IsLaplaceDatum.laplace_method` (New/Appendix/DiscreteSeries/Periods.lean).

*Proof of the theorem of Laplace's method.* Let $J(s) = g \oplus g'$, a proper homomorphism. Let $V$ be the measure of $\{\|J(s)\| \leq \beta + 1\}$, $W$ that of $\{\|J(s) - 1\| \leq (200\beta^5)^{-1}\}$, and $I = |\int\theta\,d\nu|$. The set in the statement is the set of $V$, since $\|J(s)\| = \max(\|g\|, \|g'\|)$.

The function $\theta$ is continuous, and $|\theta| \leq G$ with $G(s) = (2/\|J(s)\|)^{9N}$. Since $9N > 8N$, the decay integral gives that $G$ is integrable with $\int G \leq 16^{9N}\nu\{\|J(s) - 1\| \leq 1\} \leq 16^{9N}V$, by the lemma on the unit ball. So $\theta$ is integrable. The lemma on integration with $A$ the small ball, and the pointwise bounds, give
$$ W/4 \leq 2I + 6\beta^{-50N}16^{9N}V. $$
The covering bound with $d = \#n + \#m$ gives $V \leq \beta^{16N}W$. Here $W$ is finite, since $J$ is proper and $\nu$ is finite on compact sets. The lemma on absorbing the error gives $V \leq \beta^{20N}I$. The hypothesis on $h$ in the theorem is $h \geq 10^{30}T^3$. $\square$

**Remark (Formalization).** In the source the theorem asks for a right invariant measure that is finite on compact sets, and for a Borel structure on $S$. It does not ask that $\nu$ is a Haar measure. The source states the bound for the measure of the large set in the extended nonnegative reals. So the bound also implies that this measure is finite.

**Remark (Formalization).** The norms change inside this section. The far and near lemmas use the Frobenius norm, as do the localization theorem and the Gaussian shape. The balls of the theorem, the decay lemma and the lower bound on the small ball use the operator norm. The two norms are not compared anywhere in the argument: the near and far split is made through the noncompact parts, and the cone theorem holds at every point of $S$ without reference to a ball.
