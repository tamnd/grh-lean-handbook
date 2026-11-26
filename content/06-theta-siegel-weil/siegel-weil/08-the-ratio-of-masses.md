---
title: The ratio of masses
lean:
  - Lib/Adelic/Unitary/Defs.lean
  - Lib/SiegelWeil/Mass.lean
  - Lib/SiegelWeil/OneVector/SiegelClassSum.lean
decls:
  - New.mass
  - New.mass_pos
  - New.classSum_stdRatPoints_eq_mass
  - New.normOneLatticeVectors
  - New.classSum_card_norm_one_eq_mass
  - New.mass_eq_mass_succ_mul_normDensity
  - New.conductorIdeal
  - New.gauss_sum_sq_le
  - New.lintegral_gauss_sum_le_idealZeta
  - New.idealZeta_intAdeles_pow_le
  - New.norm_sub_one_le_of_normDensity_eq
  - New.abs_log_mass_ratio_sub_le
status: drafted
drafted_by: writer@claude-opus-5-5
---

## The ratio of masses

This section applies Siegel's formula to the vectors of norm $1$ in the standard lattice. The source does not evaluate the local densities. It shows that the finite density is close to the volume of the lattice in large rank. This gives the logarithm of the ratio of the masses in consecutive ranks up to an error that depends only on the degree of the field.

### Masses

Let $E$ be a CM field with Weil data, $[E : \mathbb{Q}] = 2f$, root discriminant $\mathrm{rd}_E$ with $|D_E| = (\mathrm{rd}_E^f)^2$, and integral finite adeles $\widehat{\mathcal O}$. For a rank $l$, let $G_f$ be the unitary group of the standard definite space $I_l$ over the finite adeles, $\Gamma$ the image of its rational points, and $K_0$ the stabilizer of $\widehat{\mathcal O}^l$.

**Definition (Mass).** The mass of the genus of $\mathcal O_E^l$ is
$$
\mathrm{mass}(l) = \sum_{\Gamma g K_0} \frac{1}{\#(\Gamma \cap g K_0 g^{-1})},
$$
the class sum `New.classSum` of the constant $1$.
Lean: `New.mass`, `New.mass_pos`, `New.classSum_stdRatPoints_eq_mass` (Lib/Adelic/Unitary/Defs.lean; Lib/SiegelWeil/Mass.lean)

The mass is positive (`mass_pos`). The class sum of $1$ for any finite index type $\kappa$ is $\mathrm{mass}(\#\kappa)$ (`classSum_stdRatPoints_eq_mass`), since a renumbering of the basis matches both pairs of subgroups.

### Vectors of norm one

**Theorem (Class sum of the vectors of norm one).** Let $E$ contain a primitive root of unity of order $5040$. Then
$$
\sum_{\Gamma g K_0} \frac{\#\{y \in E^{j+1} : \bar y^{\mathsf T} y = 1, \ g^{-1}y \in \widehat{\mathcal O}^{j+1}\}}{\#(\Gamma \cap g K_0 g^{-1})} = \mathrm{mass}(j),
$$
where the class sum on the left is in rank $j + 1$.
Lean: `New.classSum_card_norm_one_eq_mass`, `New.normOneLatticeVectors`, `New.image_normOneLatticeVectors_eq_orbit_inter` (Lib/SiegelWeil/Mass.lean)

*Proof.* Let $e$ be the last basis vector. The rational group acts transitively on the vectors of norm $1$, by Witt's theorem. The source proves the same for $K_0$ on integral vectors. There the root of unity of order $5040$ makes $E$ unramified over its real subfield at all finite places. So the vectors of norm $1$ in the lattice of $g$ form $\Gamma e \cap g K_0 e$. The stabilizer of $e$ is the group of rank $j$, embedded by $a \mapsto \mathrm{diag}(a, 1)$. The orbit count `New.classSum_card_orbit` turns the class sum in rank $j + 1$ into the class sum of $1$ in rank $j$. $\square$

**Remark (Formalization).** The class `WeilData` extends `HasPrimitiveRoot5040`, so the hypothesis holds in every use below. The count is `Set.ncard`, which is $0$ on an infinite set. Here the set is finite, since the lattice is definite.

### Siegel's formula for vectors of norm one

Let $\chi$ be the indicator of $L = \widehat{\mathcal O}^{j+1}$.

**Theorem (Siegel's formula for the masses).** For $j \ge 2$,
$$
\mathrm{mass}(j) = \mathrm{mass}(j+1) \cdot |D_E|^{1/4} \cdot \Bigl(\frac{\pi^{j+1}}{j!}\Bigr)^{f} \cdot \mathrm{normDensity}(\chi, 1).
$$
Lean: `New.mass_eq_mass_succ_mul_normDensity`, `New.classSum_eq_mul_normDensity` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean)

*Proof.* Apply Siegel's formula `New.classSum_eq_mul_normDensity` in rank $j + 1 \ge 3$, level $K_0$, to $\chi$ and $\alpha = 1$. The left class sum is $\mathrm{mass}(j)$ by the theorem above, the right one is $\mathrm{mass}(j+1)$, and the real factor at each infinite place is $\pi^{j+1}/j!$. The source writes $|D_E|^{1/4}$ as $\sqrt{\sqrt{(\mathrm{rd}_E^f)^2}}$. $\square$

### Adelic Gauss sums

The density $\mathrm{normDensity}(\chi, 1)$ is the integral over the self-adjoint finite adeles $z$ of a Gauss sum of $L$:
$$
F(z) = \int_{y \in \widehat{\mathcal O}^n} \psi_f\bigl(\tfrac12 z (\bar y^{\mathsf T} y - 1)\bigr) \, dy.
$$
Here $\psi_f$ is the finite part of the standard additive character. The bounds below are a version over all finite places at once of the Gauss sum bounds of the previous section, proved separately in Lib/SiegelWeil/Mass.lean. The semilocal results go to [Volume 10](/chapter/finite-densities/).

For a self-adjoint finite adele $b$, the conductor ideal $I_b$ is the largest ideal of $\widehat{\mathcal O}$ on which $v \mapsto \psi_f(bv)$ is trivial. It has finite index.

**Theorem (Weyl differencing over the finite adeles).** For self-adjoint $b$ and any finite adele $\Gamma$,
$$
[\widehat{\mathcal O} : I_b]^{\#n} \cdot \Bigl\| \int_{\widehat{\mathcal O}^n} \psi_f\bigl(\tfrac12 b (\bar w^{\mathsf T} w - \Gamma)\bigr) \, dw \Bigr\|^2 \le \bigl(\mathrm{vol}(\widehat{\mathcal O})^{\#n}\bigr)^2.
$$
Lean: `New.gauss_sum_sq_le`, `New.conductorIdeal` (Lib/SiegelWeil/Mass.lean)

*Proof.* The square is the integral of the autocorrelation over shifts $d$. Translation shows that it vanishes unless every $d_i$ lies in the kernel of $v \mapsto \psi_f(bv)$, a set of volume $\mathrm{vol}(\widehat{\mathcal O}) / [\widehat{\mathcal O} : I_b]$. $\square$

**Theorem (Integral of the Gauss sums).** Let $\zeta_{\widehat{\mathcal O}}(\mu) \le 2$ and $\#n \ge 2(\mu + 1)$. For every finite adele $\Gamma$,
$$
\int_b \Bigl\| \int_{\widehat{\mathcal O}^n} \psi_f\bigl(\tfrac12 b (\bar w^{\mathsf T} w - \Gamma)\bigr) \, dw \Bigr\| \, db \le \zeta_{\widehat{\mathcal O}}(\mu) \cdot \mathrm{vol}(\widehat{\mathcal O})^{\#n}.
$$
The measure on $b$ gives each coset of `New.selfAdjointCodifferent E 1` the measure $1$.
Lean: `New.lintegral_gauss_sum_le_idealZeta`, `New.selfAdjointCodifferent`, `New.lintegral_le_idealZeta_mul` (Lib/SiegelWeil/Mass.lean; Lib/Adelic/Adeles/StrongApproximation.lean)

*Proof.* Sort the $b$ by $I = I_b$. Those with a given $I$ of index $y$ lie in at most $y$ cosets of the codifferent, each of measure $1$. Weyl differencing saves $[\widehat{\mathcal O} : I]^{\#n/2} \ge [\widehat{\mathcal O} : I]^{\mu+1}$, and one factor pays for the cosets. Sum over ideals. $\square$

**Theorem (The zeta value is close to one).** Let $u, v, n$ be natural numbers with $n [E : \mathbb{Q}] \le 2^v$. Then
$$
\zeta_{\widehat{\mathcal O}}(u + v + 4)^n \le 1 + 2^{-u}.
$$
Lean: `New.idealZeta_intAdeles_pow_le`, `New.le_two_of_pow_le_ofReal` (Lib/SiegelWeil/Mass.lean)

*Proof.* Contraction to $\mathcal O_E$ keeps the index, so $\zeta_{\widehat{\mathcal O}}(\sigma) \le \zeta_E(\sigma)$, whose logarithm is at most $2[E : \mathbb{Q}] \cdot 2^{2 - \sigma}$ by the Euler product. $\square$

The lemma `le_two_of_pow_le_ofReal` gives $\zeta \le 2$ from this bound.

### The density is close to the volume

**Theorem (The finite density at one).** Let $8f \le 2^u$ and $\#n \ge 4u + 12$. Let $x \ne 0$ be a complex number with
$$
\mathrm{normDensity}(\mathbf 1_{\widehat{\mathcal O}^n}, 1) = x \cdot \mathrm{vol}(\widehat{\mathcal O})^{\#n}.
$$
Then $\|x - 1\| \le 2^{-(u+1)}$.
Lean: `New.norm_sub_one_le_of_normDensity_eq`, `New.volÔ` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean; Lib/Adelic/Adeles/AdditiveCharacter.lean)

*Proof.* The density is $\int F \neq 0$, so $F$ is integrable. The zeta lemma with $u + 1$, $v = u$, $n = 1$ gives $\zeta_{\widehat{\mathcal O}}(2u + 5) \le 1 + 2^{-(u+1)} \le 2$, and $2(2u + 6) \le \#n$. So the integral bound gives
$$
\int \|F\| \le \bigl(1 + 2^{-(u+1)}\bigr) \mathrm{vol}(L).
$$

For $z$ in the codifferent $C$, of measure $1$, and $y \in L$, write $\bar y^{\mathsf T} y - 1 = t + \bar t$ with $t$ integral. Then $\psi_f(\frac12 z(t + \bar t)) = \psi_f(zt) = 1$, so $\int_C F = \mathrm{vol}(L)$. The integral over the complement is $(x - 1)\mathrm{vol}(L)$, and the norms of the two parts add up to at most $\int \|F\|$. $\square$

**Remark (Formalization).** The hypothesis $x \neq 0$ handles a junk value: `New.normDensity` is $0$ when its integrand is not integrable. With $x \neq 0$ the density is a true integral. Below, $x \neq 0$ follows from Siegel's formula, because $\mathrm{mass}(j) > 0$.

### The ratio of consecutive masses

**Theorem (Masses).** Let $8f \le 2^u$ and $j \ge 4u + 12$. Then
$$
\Bigl| \log \mathrm{mass}(j+1) - \log \mathrm{mass}(j) - f \Bigl( \bigl(j + \tfrac12\bigr) \log \mathrm{rd}_E + \log j! - (j + 1) \log 2\pi \Bigr) \Bigr| \le \frac{2}{2^u}.
$$
Lean: `New.abs_log_mass_ratio_sub_le` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean)

*Proof.* Write $\mathrm{normDensity}(\chi, 1) = x \cdot \mathrm{vol}(\widehat{\mathcal O})^{j+1}$ in Siegel's formula for the masses. The masses are positive, so $x \neq 0$. The rank is $j + 1 \ge 4u + 12$, so the previous theorem gives $\|x - 1\| \le 2^{-(u+1)} \le \frac12$. With $\mathrm{vol}(\widehat{\mathcal O}) = ((\mathrm{rd}_E/2)^f)^{-1}$, the difference in the claim is $-\log\|x\|$, and
$$
|\log \|x\|| \le |\log(1 + (x - 1))| \le \tfrac32 \|x - 1\| \le 4 \cdot 2^{-(u+1)} = \frac{2}{2^u}. \qquad \square
$$

A larger $u$ gives a smaller error and needs a larger rank. The error does not depend on the discriminant.

**Remark (Formalization).** The classical mass formula gives the mass exactly, as a product of $L$-values and local factors. The source names W. T. Gan, J. Hanke and J.-K. Yu, Duke Math. J. 107 (2001), and M. Kirschmer, Definite quadratic and hermitian forms with small class number (2016), 4.2.7 and 4.2.9. This chapter has not checked those numbers against the texts. The source form is weaker: it gives only the ratio in consecutive ranks, only for $j \ge 4u + 12$, with an explicit error $2/2^u$ in place of the $L$-value factor, and only for fields with Weil data. The number $x$ is chosen by `obtain`. It is the density divided by $\mathrm{vol}(\widehat{\mathcal O})^{j+1}$.

The frame mass estimate in [Poincaré series](/chapter/poincare-series/) uses this estimate.
