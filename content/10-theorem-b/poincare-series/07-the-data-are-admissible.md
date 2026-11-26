---
title: The data are admissible
lean:
  - New/Spanning/Unfolding/FrameMass.lean
  - New/Spanning/Unfolding/FillingAdmissible.lean
decls:
  - New.Data.log_pow_div_pow_sub_one_le
  - New.Data.abs_sum_log_mass_ratio_sub_le
  - New.Data.two_div_and_inv_sqrt_deltaE_mem_Icc
  - New.Data.inv_unitSphereMass_le_pow
  - New.Data.inv_pow_le_frameMass
  - New.Data.log_prod_unitSphereMass
  - New.Data.prod_frameMass_mul_le
  - New.Data.prod_frameMass_mul_openCellConst_eq
  - New.Data.filling_fits
  - New.Data.card_besselSystem_le_add_pow
  - New.Data.card_besselCoord_le_pow
  - New.Data.log_filling_besselDegree_mem_Icc
  - New.Data.relIndex_latticeStabilizer
  - New.Data.card_classes_eq_card_mul_pow_mul_mass
  - New.Data.card_mul_prod_frameMass_le
  - New.Data.scaledSiegelConst_le
  - New.Data.filling_reduction_surjective
  - New.Data.mainSecondMoment_div_identitySecondMoment_eq
  - New.Data.mainSecondMoment_div_identitySecondMoment_mem_Icc
  - New.Data.N_le_pow
status: drafted
drafted_by: writer@claude-opus-5-5
---

## The data are admissible

The general results of this chapter are about filling data $S$ with the standing hypotheses `New.Filling.IsAdmissible`. This section shows that the filling data $D.\mathrm{filling}$ of admissible data $D$ fit the space $Y_0$ and satisfy these hypotheses. The work is a computation of sizes. Its two inputs are the mass of a unit sphere and the ratio of masses in consecutive ranks.

The data have a CM field $E$ with $f$ infinite places, root discriminant $\mathrm{rd}$, a generator $\varpi$ of the different, a prime level $N$, a weight $b$, a length $x$ and ranks $k \le r$ with $r = k + 2\varrho + 1$. The size conditions of the data are used through `New.Data.le_of_hasLogBound` and `New.Data.nat_le_of_hasLogBound`. Each use below names the inequality that it takes. The data are fixed in [Theorem B: the plan](/chapter/theorem-b-plan/#conventions-that-change-the-meaning).

### Sphere and frame masses

At an infinite place $v$ write $w_v = |\varpi|_v$. For $l \ge 0$ put
$$
\mathrm{sph}_l(v) = \frac{(2\pi)^l}{w_v^{\,l - 1/2}\,(l-1)!}, \qquad \mathrm{fr}_v = N^k \prod_{k \le i < r}\mathrm{sph}_{i+1}(v).
$$
For $l \ge 1$, $\mathrm{sph}_l(v)$ is the mass of the unit sphere of $\mathbb C^l$ for the measure $dy/d\langle y,y\rangle$, when $\mathbb C$ carries $2/w_v$ and $\mathbb R$ carries $w_v^{-1/2}$ times Lebesgue measure. Both numbers are positive, because $w_v > 0$.

**Remark (Formalization).** In Lean $(l - 1)!$ uses truncated subtraction, so for $l = 0$ the factor is $0! = 1$ and $\mathrm{sph}_0(v) = w_v^{1/2}$. Only $l \ge k + 1$ and $l = k$ occur below, with $k \ge 1$.

**Lemma (Size of the different).** At every infinite place, $2/w_v$ and $w_v^{-1/2}$ lie in $[b^{-1}, 1]$.
Lean: `New.Data.two_div_and_inv_sqrt_deltaE_mem_Icc` (New/Spanning/Unfolding/FrameMass.lean).

*Proof.* The size conditions give $2 \le w_v \le b$. Then $2/w_v \le 1$ and $2/w_v \ge 1/w_v \ge b^{-1}$. Also $1 \le \sqrt{w_v} \le b$, because $w_v \le b \le b^2$. Invert. $\square$

**Lemma (Small spheres).** For $l \le r$, $\mathrm{sph}_l(v)^{-1} \le x^{18l}$.
Lean: `New.Data.inv_unitSphereMass_le_pow` (New/Spanning/Unfolding/FrameMass.lean).

*Proof.* The size conditions give $1 \le w_v$ and $w_v r \le x^{18}$. Then $w_v^{l - 1/2} \le w_v^l$ and $(l-1)! \le l! \le l^l \le r^l$. Since $2\pi \ge 1$,
$$
\mathrm{sph}_l(v)^{-1} \le w_v^{l-1/2}(l-1)! \le (w_v r)^l \le x^{18l}. \qquad \square
$$

**Lemma (Lower bound for the frame mass).** $\mathrm{fr}_v \ge b^{-(\varrho+1)r}$ at every infinite place.
Lean: `New.Data.inv_pow_le_frameMass` (New/Spanning/Unfolding/FrameMass.lean).

*Proof.* There are $r - k = 2\varrho + 1$ factors. Each is at least $x^{-18(i+1)} \ge x^{-18r}$ by the last lemma and $x \ge 1$. So the product is at least $x^{-18r(2\varrho+1)}$. The size conditions give $x^{36} \le b$, and $18r(2\varrho+1) \le 36(\varrho+1)r$. So the product is at least $b^{-(\varrho+1)r}$. The factor $N^k$ is at least $1$. $\square$

**Lemma (Product over the places).** $\log\prod_v \mathrm{sph}_{i+1}(v) = -f\bigl((i+\tfrac12)\log\mathrm{rd} + \log i! - (i+1)\log 2\pi\bigr)$.
Lean: `New.Data.log_prod_unitSphereMass` (New/Spanning/Unfolding/FrameMass.lean).

*Proof.* The product of the $w_v$ over the $f$ places is $\mathrm{rd}^f$ (`New.Parameters.prod_deltaE_eq_rootDiscr_pow`). So the product of the $\mathrm{sph}_{i+1}(v)$ is $(2\pi)^{(i+1)f}/\bigl((\mathrm{rd}^f)^{i+1/2}(i!)^f\bigr)$. Take the logarithm. $\square$

The *ratio of masses* in [Siegel's formula](/chapter/siegel-weil/#the-ratio-of-masses) says: if $8f \le 2^u$ and $j \ge 4u + 12$, then $\log\mathrm{mass}(j+1) - \log\mathrm{mass}(j)$ differs from $f\bigl((j+\tfrac12)\log\mathrm{rd} + \log j! - (j+1)\log 2\pi\bigr)$ by at most $2/2^u$ (`New.abs_log_mass_ratio_sub_le`). Here $\mathrm{mass}(l)$ is the mass of the genus of $\mathcal O_E^l$.

**Lemma (Sum of the errors).** The sum over $k \le i < r$ of these differences, with $u = \varrho$, has absolute value at most $\log(1 + b^{-9}) - 4f/N$.
Lean: `New.Data.abs_sum_log_mass_ratio_sub_le` (New/Spanning/Unfolding/FrameMass.lean).

*Proof.* The size conditions give $8f \le 2^\varrho$ and $4\varrho + 12 \le k \le i$. So each term is at most $2/2^\varrho$, and the sum is at most $(r-k)\cdot 2/2^\varrho$. The size conditions also give $(r-k)\,2/2^\varrho + 4f/N \le 2b^{-9}/(b^{-9}+2)$, and $2y/(y+2) \le \log(1+y)$ for $y \ge 0$. $\square$

**Lemma.** $\log\bigl(N^k/(N^k-1)\bigr) \le 2/N$.
Lean: `New.Data.log_pow_div_pow_sub_one_le` (New/Spanning/Unfolding/FrameMass.lean).

*Proof.* $\log y \le y - 1$, so the left side is at most $1/(N^k - 1)$. As $N \ge 2$ and $N^k \ge N$, we have $N \le 2(N^k - 1)$. $\square$

**Theorem (Frame mass estimate).**
$$
\Bigl(\prod_v \mathrm{fr}_v\Bigr)\,\mathrm{mass}(r)\,\Bigl(\frac{N^k}{N^k-1}\Bigr)^{2f} \le (1 + b^{-9})\,N^{kf}\,\mathrm{mass}(k).
$$
Lean: `New.Data.prod_frameMass_mul_le` (New/Spanning/Unfolding/FrameMass.lean).

*Proof.* Exchange the products: $\prod_v\mathrm{fr}_v = N^{kf}P$ with $P = \prod_{k\le i<r}\prod_v\mathrm{sph}_{i+1}(v)$. By the product lemma and the ratio of masses, $\log\prod_v\mathrm{sph}_{i+1}(v)$ differs from $\log\mathrm{mass}(i) - \log\mathrm{mass}(i+1)$ by at most $2/2^\varrho$. Sum over $i$. The mass terms telescope, and the sum of the errors gives
$$
\log\mathrm{mass}(r) - \log\mathrm{mass}(k) + \log P \le \log(1+b^{-9}) - 4f/N.
$$
The last lemma gives $2f\log(N^k/(N^k-1)) \le 4f/N$. Add the two inequalities and take the exponential. Multiply by $N^{kf}$. $\square$

**Lemma (Frame masses and the Siegel constant).** With $c_G$ the open cell constant and $c_S$ the Siegel constant of the filling data,
$$
\Bigl(\prod_v\mathrm{fr}_v\Bigr)\,c_G^{\,f}\,|\mathrm{disc}\,E|^{\varrho/2} = c_S\,N^{2kf}\,\mathrm{vol}(\widehat{\mathcal O})^{\varrho+1+2\varrho(\varrho+k)}.
$$
Lean: `New.Data.prod_frameMass_mul_openCellConst_eq` (New/Spanning/Unfolding/FrameMass.lean).

*Proof.* Here $c_G = \mathrm{vol}\,U(k)\,(2\pi^k/(k-1)!)/\mathrm{vol}\,U(r)$, $c_S = (\pi^k/((k-1)!N^k))^f|\mathrm{disc}\,E|^{1/4}\mathrm{vol}(\widehat{\mathcal O})^k$, $\mathrm{vol}(\widehat{\mathcal O}) = (2/\mathrm{rd})^f$ and $|\mathrm{disc}\,E| = \mathrm{rd}^{2f}$. Both sides are positive. The volume of $U(r)$ is that of $U(k)$ times $\prod_{k\le i<r}2\pi^{i+1}/i!$. So the logarithms of both sides are linear forms in $\log 2$, $\log\pi$, $\log N$, $\log\mathrm{rd}$ and the $\log i!$. The sum of the $i$ with $k \le i < r$ is $(2\varrho+1)(k+\varrho)$. With this, the two forms have the same coefficients. $\square$

### The fit and the Bessel bounds

**Lemma (Fit).** The filling data of $D$ fit $Y_0$ in the sense of `New.Filling.Fits`, with the grading of $Y_0$ and the inverse of the scalar given by the lattice scale.
Lean: `New.Data.filling_fits` (New/Spanning/Unfolding/FillingAdmissible.lean).

*Proof.* By the choice of $Y_0$, its finite frame is the graded lattice basis times an integral $\gamma$ that is $1$ at the chosen places. The graded lattice basis scales only the string by the lattice scale $u$. So it is $u$ times the lattice basis of the filling data, multiplied by $u^{-1}$ on $X_0$. The remaining fields of `Fits` are the kernel, the point $\gamma$, and the fact that scalars are central. $\square$

**Lemma (Number of Bessel coordinates).** At each infinite place the Bessel system has at most $(k+a)^k \le b^{2k}$ coordinates. The tensor product has at most $b^{2kf}$ coordinates.
Lean: `New.Data.card_besselSystem_le_add_pow`, `New.Data.card_besselCoord_le_pow` (New/Spanning/Unfolding/FillingAdmissible.lean).

*Proof.* The coordinates are in bijection with a basis of a Schur module of $U(X_0)$. Its weight has one row of length $a' \le a$ and no columns of height $2$ to $k-1$. So the basis is in bijection with the monomials of degree $a'$ in $k$ variables. There are $\binom{k+a'-1}{a'} \le \binom{k+a}{k} \le (k+a)^k$ of them. The size conditions give $k + a \le b^2$. Multiply over the $f$ places. $\square$

**Lemma (Degree).** Let $\varsigma$ be the target parameter at $v$, $W_v$ the weight at $v$ and $m = r - k + 1$. Then $\log\deg + f\sum_{k-1\le l<r}\log l!$ lies between $\sum_v m(k-1)\log W_v$ and $\sum_v m r(\log W_v + x^{-1})$.
Lean: `New.Data.log_filling_besselDegree_mem_Icc` (New/Spanning/Unfolding/FillingAdmissible.lean).

*Proof.* The Weyl dimension formula gives $\deg = \exp\sum_v\sum_{k-1\le l<r}\bigl(\sum_{i<l}\log(\varsigma_i - \varsigma_l) - \log l!\bigr)$. For $i < l$, $1 \le \varsigma_i - \varsigma_l \le w_{l+2-k}(v)$, the lift weight. For the lower bound keep only the $i < k - 1$, where each difference is at least $W_v$. For the upper bound use $\log w_{l+2-k}(v) \le \log W_v + x^{-1}$ and $l < r$. There are $m$ values of $l$. $\square$

### Indices, classes and the second moments

**Lemma (Index of the lattice stabilizer).** The elements of $U(X_0)(\mathbb A_f)$ that map into the lattice stabilizer have index $(N^k - 1)^f$ in the integral points.
Lean: `New.Data.relIndex_latticeStabilizer` (New/Spanning/Unfolding/FillingAdmissible.lean).

*Proof.* By [the climbing section](/chapter/poincare-series/#climbing-the-flags), an integral $x$ lies in this group if and only if its row $k_0$ is the unit vector modulo $\pi$. That is, at each of the $f$ places $w$ above $N$, the inverse transpose of the reduction of $x$ fixes the unit vector of $\mathbb F_N^k$. The group is the preimage of a product of stabilizers, and reduction is onto. A stabilizer of a nonzero vector in $GL_k(\mathbb F_N)$ has index $N^k - 1$, the size of its orbit. $\square$

**Lemma (Number of classes).** $n_X = |\bar H|\,(N^k - 1)^f\,\mathrm{mass}(k)$, with $\bar H$ the reduced image of $H$.
Lean: `New.Data.card_classes_eq_card_mul_pow_mul_mass` (New/Spanning/Unfolding/FillingAdmissible.lean).

*Proof.* The classes have trivial automorphism groups. So $n_X$ is the index of the level of $X_0$ in the integral points, times $\mathrm{mass}(k)$ ([class sums](/chapter/automorphic-forms/#hecke-operators-and-class-sums)). The level lies in the group of the last lemma. Its index there is $|\bar H|$ (`New.Filling.relIndex_comap_principalLevel`). Multiply the indices. $\square$

**Theorem (Mean values).** Let $d_v$ and $\deg_v$ be the number of coordinates and the degree of the Bessel system at $v$. Then $|\bar H|\,n_X\prod_v\mathrm{fr}_v d_v^2/\deg_v$ and $|\bar H|^2\,\mathrm{mass}(k)\prod_v N^k\mathrm{fr}_v d_v^2/\deg_v$ are at most $(1+b^{-9})$ times the main second moment $\mathrm{msm} = (n_X d)^2/(\deg\cdot\mathrm{mass}(r))$.
Lean: `New.Data.card_mul_prod_frameMass_le` (New/Spanning/Unfolding/FillingAdmissible.lean).

*Proof.* By the last lemma, $\mathrm{msm} = (|\bar H|(N^k-1)^f\mathrm{mass}(k)\,d)^2/(\deg\cdot\mathrm{mass}(r))$. Put $\mu = \mathrm{msm}/(N^{kf}\mathrm{mass}(k))$. The second number equals $(\prod_v\mathrm{fr}_v)\,\mathrm{mass}(r)\,(N^k/(N^k-1))^{2f}\mu$. The frame mass estimate bounds it by $(1+b^{-9})N^{kf}\mathrm{mass}(k)\mu = (1+b^{-9})\,\mathrm{msm}$. The first number is the second one with $N^{kf}$ replaced by $(N^k-1)^f$, so it is smaller. $\square$

In Lean the second number is written as $\prod_v\mathrm{sph}_k(v)c_v$ with $c_v = \mathrm{fr}_vN^kd_v^2/(\mathrm{sph}_k(v)\deg_v)$. The factors $\mathrm{sph}_k(v)$ cancel.

**Lemma (Siegel constant).** The scaled Siegel constant $|\bar S|\,|\bar U|\,n_X c_S$ is at most $(1+b^{-9})\,\mathrm{msm}\,\deg\,c_G^{\,f}\,\mathrm{vol}(\widehat{\mathcal O})^{-n}\,(\nu\Lambda/d)^2$, with $\nu$ the unipotent covolume and $\Lambda$ the frame scale product.
Lean: `New.Data.scaledSiegelConst_le` (New/Spanning/Unfolding/FillingAdmissible.lean).

*Proof.* The definition of $\nu$ gives $\nu\Lambda = |\bar U|\,N^{-kf}\,\mathrm{vol}(\widehat{\mathcal O})^{-\varrho(\varrho+k)}|\mathrm{disc}\,E|^{\varrho/4}$. Insert this, $|\bar S| = |\bar H|\,|\bar U|$ ([reduced groups](/chapter/poincare-series/#reduced-groups-and-the-structure-of-a-term)) and $c_S$ from the frame mass lemma. The powers of $N$, of the volume and of the discriminant cancel. What is left is the first number of the mean value theorem times the factor on the right. $\square$

**Lemma (Ratio of the second moments).** With $\mathrm{ism} = |\bar S|\,n_Xd$ the identity second moment, $\mathrm{msm}/\mathrm{ism} = d\,(N^k-1)^f\mathrm{mass}(k)/(\deg\cdot\mathrm{mass}(r)\,|\bar U|)$.
Lean: `New.Data.mainSecondMoment_div_identitySecondMoment_eq` (New/Spanning/Unfolding/FillingAdmissible.lean).

*Proof.* $\mathrm{msm}/\mathrm{ism} = n_Xd/(|\bar S|\deg\,\mathrm{mass}(r))$. Insert $|\bar S| = |\bar H||\bar U|$ and the number of classes. $\square$

**Theorem (Range of the ratio).** $b^{11kf} \le \mathrm{msm}/\mathrm{ism} \le (M/b^6)^{kf}$.
Lean: `New.Data.mainSecondMoment_div_identitySecondMoment_mem_Icc` (New/Spanning/Unfolding/FillingAdmissible.lean).

*Proof.* Insert into the last lemma $|\bar U| = M^{f\varrho(2k+2\varrho+1)}$, the degree lemma, the sum of the mass errors and $\lambda \le \log N \le \lambda + \sqrt{\log b}$ (`New.Data.log_N_mem_Icc_logLevelTarget`). The mass ratios telescope and the factorials cancel except $(k-1)!$. The size conditions bound what is left by $fk\log b/4$. This gives $|\log(\mathrm{msm}/\mathrm{ism}) - fk(\log M - \tfrac{15}{2}\log b) - \log(d\,((k-1)!)^f)| \le fk\log b/4$ (`New.Data.abs_log_mainSecondMoment_div_identitySecondMoment_sub_le`). The number $d\,((k-1)!)^f$ lies between $1$ and $b^{5kf/4}$, by the count of coordinates and $(k+a)k \le b^{5/4}$. The size conditions give $b^{19} \le M$. So the logarithm lies between $fk(19 - 15/2 - 1/4)\log b \ge 11fk\log b$ and $fk(\log M - 15/2\log b + 5/4\log b + 1/4\log b) = fk(\log M - 6\log b)$. $\square$

### The standing hypotheses

**Lemma.** Reduction at the chosen places maps the lattice stabilizer onto the residue group. Also $N \le b^{60n}$.
Lean: `New.Data.filling_reduction_surjective`, `New.Data.N_le_pow` (New/Spanning/Unfolding/FillingAdmissible.lean).

*Proof.* Lift the residues of $x$ to an integral matrix. By [the Poincaré series section](/chapter/poincare-series/#poincar-series-and-the-petersson-formula), the lift is in the lattice stabilizer and reduces to $x$. For the second claim, $\log N \le 30(2\varrho+2)\log b = 60n\log b$. $\square$

**Theorem (Admissibility).** The filling data of $D$ satisfy `New.Filling.IsAdmissible`.
Lean: an unnamed instance of `New.Filling.IsAdmissible` (New/Spanning/Unfolding/FillingAdmissible.lean).

*Proof.* Each field is proved above or by the size conditions. The level is the preimage of $K(M)$ (`New.Data.levelX_zero_eq_comap`). Reduction is onto. $|\varpi|_v \le b$. $1 \le |\kappa_v| \le b^{23}$, where $|\kappa_v| = Mw_v/2\pi$. $N \le b^{60n}$. The two bounds for $\mathrm{msm}$ are the range of the ratio, since $\mathrm{ism} > 0$. The coordinates are at most $b^{2kf}$. The index is $(N^k-1)^f \ge (N^k/b)^f$, because $N^k/b \le N^k/2 \le N^k - 1$. The Siegel constant bound is the last lemma of the previous part. $\square$

**Remark (Formalization).** The theorem is an instance without a name, at [FillingAdmissible.lean](lean:New/Spanning/Unfolding/FillingAdmissible.lean#L743). So the Lean line above gives the class and not a name. Lean finds it by type class search wherever a result of this chapter is applied to $D.\mathrm{filling}$. The index in `le_relIndex` is `Subgroup.relIndex`, which is $0$ for an infinite index. Here it is finite and equal to $(N^k-1)^f$, so the junk value does not occur.
