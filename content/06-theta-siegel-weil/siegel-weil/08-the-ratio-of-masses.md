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

This section applies Siegel's formula to the vectors of norm $1$ in the standard lattice. The result compares the masses of the standard genus in two consecutive ranks. The source does not evaluate the local densities. It shows that the finite density is close to the volume of the lattice when the rank is large. The output is an estimate for the logarithm of the ratio of masses, with an error that depends on the field only through its degree.

### Masses

Let $E$ be a CM field with Weil data. Write $f$ for the number of infinite places of $E$, so $[E : \mathbb{Q}] = 2f$. Write $\mathrm{rd}_E$ for the root discriminant, so $|D_E| = (\mathrm{rd}_E^f)^2$. Let $\widehat{\mathcal O}$ be the integral finite adeles. For a rank $l$, let $G_f$ be the unitary group of the standard definite space $I_l$ over the finite adeles, $\Gamma$ the image of its rational points, and $K_0$ the stabilizer of $\widehat{\mathcal O}^l$.

**Definition (Mass).** The mass of the genus of $\mathcal O_E^l$ is
$$
\mathrm{mass}(l) = \sum_{\Gamma g K_0} \frac{1}{\#(\Gamma \cap g K_0 g^{-1})},
$$
the class sum `New.classSum` of the constant $1$.
Lean: `New.mass`, `New.mass_pos`, `New.classSum_stdRatPoints_eq_mass` (Lib/Adelic/Unitary/Defs.lean; Lib/SiegelWeil/Mass.lean)

The mass is positive, by `mass_pos`. The class sum of $1$ for any finite index type $\kappa$ is $\mathrm{mass}(\#\kappa)$, by `classSum_stdRatPoints_eq_mass`. A renumbering of the basis is an isomorphism that matches both pairs of subgroups.

### Vectors of norm one

For $g \in G_f$ of rank $j + 1$, the vectors of norm $1$ in the lattice of $g$ are the $y \in E^{j+1}$ with $\bar y^{\mathsf T} y = 1$ and $g^{-1} y \in \widehat{\mathcal O}^{j+1}$.

**Theorem (Class sum of the vectors of norm one).** Let $E$ contain a primitive root of unity of order $5040$. Then
$$
\sum_{\Gamma g K_0} \frac{\#\{y \in E^{j+1} : \bar y^{\mathsf T} y = 1, \ g^{-1}y \in \widehat{\mathcal O}^{j+1}\}}{\#(\Gamma \cap g K_0 g^{-1})} = \mathrm{mass}(j),
$$
where the class sum on the left is in rank $j + 1$.
Lean: `New.classSum_card_norm_one_eq_mass`, `New.normOneLatticeVectors`, `New.image_normOneLatticeVectors_eq_orbit_inter` (Lib/SiegelWeil/Mass.lean)

*Proof.* Let $e$ be the last basis vector. By Witt's theorem over $E$, the rational group moves any vector of norm $1$ to any other. The source proves the same for integral vectors and $K_0$, with $E$ unramified over its real subfield at all finite places. The root of unity of order $5040$ gives this. So the image of the vectors of norm $1$ in the lattice of $g$ is $\Gamma e \cap g K_0 e$. The stabilizer of $e$ is the group of rank $j$, embedded by $a \mapsto \mathrm{diag}(a, 1)$. The element $\mathrm{diag}(a, 1)$ is rational, or integral, exactly when $a$ is. The orbit count `New.classSum_card_orbit` then turns the class sum in rank $j + 1$ into the class sum of $1$ in rank $j$. $\square$

The class `WeilData` extends `HasPrimitiveRoot5040`, so the hypothesis holds for every field in the uses below.

**Remark (Formalization).** The count is `Set.ncard`, which is $0$ on an infinite set. The set of vectors of norm $1$ in a definite lattice is finite, so the count is the true count here.

### Siegel's formula for vectors of norm one

Apply Siegel's formula `New.classSum_eq_mul_normDensity` from the section on one vector to the space of rank $j + 1$, the level $K_0$, the indicator $\chi$ of $L = \widehat{\mathcal O}^{j+1}$, and the norm $\alpha = 1$. The indicator is fixed by $K_0$ and has compact support. The two class sums in the formula are $\mathrm{mass}(j)$ and $\mathrm{mass}(j + 1)$.

**Theorem (Siegel's formula for the masses).** For $j \ge 2$,
$$
\mathrm{mass}(j) = \mathrm{mass}(j+1) \cdot |D_E|^{1/4} \cdot \Bigl(\frac{\pi^{j+1}}{j!}\Bigr)^{f} \cdot \mathrm{normDensity}(\chi, 1).
$$
Lean: `New.mass_eq_mass_succ_mul_normDensity`, `New.classSum_eq_mul_normDensity` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean)

*Proof.* Siegel's formula needs rank at least $3$, which is $j + 1 \ge 3$. The left class sum is the class sum of the number of $x \in E^{j+1}$ with $\bar x^{\mathsf T} x = 1$ and $\chi(g^{-1}x) = 1$. This is $\mathrm{mass}(j)$ by the class sum of the vectors of norm one. The right class sum is $\mathrm{mass}(j+1)$. The real factor at each infinite place is $\pi^{j+1}/j!$ at $\alpha = 1$. The source writes $|D_E|^{1/4}$ as $\sqrt{\sqrt{(\mathrm{rd}_E^f)^2}}$. $\square$

The Lean statement is an equality of complex numbers. The masses are real and are coerced.

### Adelic Gauss sums

The density $\mathrm{normDensity}(\chi, 1)$ is the integral over the self-adjoint finite adeles $z$ of a Gauss sum of $L$:
$$
F(z) = \int_{y \in \widehat{\mathcal O}^n} \psi_f\bigl(\tfrac12 z (\bar y^{\mathsf T} y - 1)\bigr) \, dy.
$$
Here $\psi_f$ is the finite part of the standard additive character. This section uses a version of the Gauss sum bounds of the previous section that works over $\widehat{\mathcal O}$ at all finite places at once. It is a separate development in Lib/SiegelWeil/Mass.lean. The semilocal results of the previous section go to [Volume 10](/chapter/finite-densities/) instead.

For a self-adjoint finite adele $b$, the conductor ideal $I_b$ is the largest ideal of $\widehat{\mathcal O}$ on which $v \mapsto \psi_f(bv)$ is trivial. It has finite index.

**Theorem (Weyl differencing over the finite adeles).** For self-adjoint $b$ and any finite adele $\Gamma$,
$$
[\widehat{\mathcal O} : I_b]^{\#n} \cdot \Bigl\| \int_{\widehat{\mathcal O}^n} \psi_f\bigl(\tfrac12 b (\bar w^{\mathsf T} w - \Gamma)\bigr) \, dw \Bigr\|^2 \le \bigl(\mathrm{vol}(\widehat{\mathcal O})^{\#n}\bigr)^2.
$$
Lean: `New.gauss_sum_sq_le`, `New.conductorIdeal` (Lib/SiegelWeil/Mass.lean)

*Proof.* The square is the integral of the autocorrelation over shifts $d$. Translation of one entry of $w$ multiplies the autocorrelation at $d$ by $\psi_f(b d_i v)$. So the autocorrelation vanishes unless every $d_i$ lies in the kernel $K$ of the character. The volume of $K \cap \widehat{\mathcal O}$ is $\mathrm{vol}(\widehat{\mathcal O}) / [\widehat{\mathcal O} : I_b]$. $\square$

**Theorem (Integral of the Gauss sums).** Let $\zeta_{\widehat{\mathcal O}}(\mu) \le 2$ and $\#n \ge 2(\mu + 1)$. For every finite adele $\Gamma$,
$$
\int_b \Bigl\| \int_{\widehat{\mathcal O}^n} \psi_f\bigl(\tfrac12 b (\bar w^{\mathsf T} w - \Gamma)\bigr) \, dw \Bigr\| \, db \le \zeta_{\widehat{\mathcal O}}(\mu) \cdot \mathrm{vol}(\widehat{\mathcal O})^{\#n}.
$$
The measure on $b$ gives each coset of `New.selfAdjointCodifferent E 1` the measure $1$.
Lean: `New.lintegral_gauss_sum_le_idealZeta`, `New.selfAdjointCodifferent`, `New.lintegral_le_idealZeta_mul` (Lib/SiegelWeil/Mass.lean; Lib/Adelic/Adeles/StrongApproximation.lean)

*Proof.* Sort the $b$ by $I = I_b$. The $b$ with a given $I$ of index $y$ lie in at most $y$ cosets of the codifferent, one for each character of $\widehat{\mathcal O}/I$. Each coset has measure $1$. Weyl differencing saves $[\widehat{\mathcal O} : I]^{\#n/2}$, which is at least $[\widehat{\mathcal O} : I]^{\mu+1}$. One factor of $[\widehat{\mathcal O} : I]$ pays for the cosets. The summation lemma over ideals gives the bound. $\square$

**Theorem (The zeta value is close to one).** Let $u, v, n$ be natural numbers with $n [E : \mathbb{Q}] \le 2^v$. Then
$$
\zeta_{\widehat{\mathcal O}}(u + v + 4)^n \le 1 + 2^{-u}.
$$
Lean: `New.idealZeta_intAdeles_pow_le`, `New.le_two_of_pow_le_ofReal` (Lib/SiegelWeil/Mass.lean)

*Proof.* Contraction to $\mathcal O_E$ is injective on ideals of finite index and keeps the index. So $\zeta_{\widehat{\mathcal O}}(\sigma)$ is at most the Dedekind zeta value $\zeta_E(\sigma)$, an Euler product. Its logarithm is at most $2[E : \mathbb{Q}] \cdot 2^{2 - \sigma}$. The rest is an inequality between real numbers. $\square$

The lemma `le_two_of_pow_le_ofReal` gives $\zeta \le 2$ from this bound, which is the hypothesis of the integral bound.

### The density is close to the volume

**Theorem (The finite density at one).** Let $8f \le 2^u$ and $\#n \ge 4u + 12$. Let $x \ne 0$ be a complex number with
$$
\mathrm{normDensity}(\mathbf 1_{\widehat{\mathcal O}^n}, 1) = x \cdot \mathrm{vol}(\widehat{\mathcal O})^{\#n}.
$$
Then $\|x - 1\| \le 2^{-(u+1)}$.
Lean: `New.norm_sub_one_le_of_normDensity_eq`, `New.volÔ` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean; Lib/Adelic/Adeles/AdditiveCharacter.lean)

*Proof.* The density is $\int F$. It is not zero, because $x \neq 0$. So $F$ is integrable.

*Step 1: the zeta bound.* Apply the zeta lemma with $u + 1$ in place of $u$, $v = u$ and $n = 1$. The hypothesis $[E : \mathbb{Q}] = 2f \le 2^u$ follows from $8f \le 2^u$. This gives $\zeta_{\widehat{\mathcal O}}(2u + 5) \le 1 + 2^{-(u+1)}$, so in particular $\zeta \le 2$. The rank condition $2(2u + 6) \le \#n$ is $4u + 12 \le \#n$. So the integral bound gives
$$
\int \|F\| \le \bigl(1 + 2^{-(u+1)}\bigr) \mathrm{vol}(L).
$$

*Step 2: the main part.* Let $C$ be the codifferent `selfAdjointCodifferent E 1`. It has measure $1$. For $z \in C$ and $y \in L$, write $\bar y^{\mathsf T} y - 1 = t + \bar t$ with $t$ integral. Then $\psi_f(\frac12 z(t + \bar t)) = \psi_f(zt) = 1$. So $F = \mathrm{vol}(L)$ on $C$, and $\int_C F = \mathrm{vol}(L)$.

*Step 3.* The integral over the complement of $C$ is $(x - 1)\mathrm{vol}(L)$. The norms of the two parts add up to at most $\int \|F\|$. Subtract $\mathrm{vol}(L)$ and divide by it. $\square$

**Remark (Formalization).** The hypothesis $x \neq 0$ handles a junk value. The density `New.normDensity` is $0$ when its integrand is not integrable, as the section on one vector records. If the density is $0$, the proof has no integrability and no bound. With $x \neq 0$ the density is a true integral. In the use below, $x \neq 0$ follows from Siegel's formula, because $\mathrm{mass}(j) > 0$.

### The ratio of consecutive masses

**Theorem (Masses).** Let $8f \le 2^u$ and $j \ge 4u + 12$. Then
$$
\Bigl| \log \mathrm{mass}(j+1) - \log \mathrm{mass}(j) - f \Bigl( \bigl(j + \tfrac12\bigr) \log \mathrm{rd}_E + \log j! - (j + 1) \log 2\pi \Bigr) \Bigr| \le \frac{2}{2^u}.
$$
Lean: `New.abs_log_mass_ratio_sub_le` (Lib/SiegelWeil/OneVector/SiegelClassSum.lean)

*Proof.* Write the density at $1$ of the indicator of $\widehat{\mathcal O}^{j+1}$ as $x \cdot \mathrm{vol}(\widehat{\mathcal O})^{j+1}$. Siegel's formula for the masses gives
$$
\mathrm{mass}(j) = \mathrm{mass}(j+1) \cdot |D_E|^{1/4} \Bigl(\frac{\pi^{j+1}}{j!}\Bigr)^f \cdot x \cdot \mathrm{vol}(\widehat{\mathcal O})^{j+1}.
$$
The masses are positive, so $x \neq 0$. The rank is $j + 1 \ge 4u + 12$, so the previous theorem gives $\|x - 1\| \le 2^{-(u+1)} \le \frac12$. Take logarithms, with $\mathrm{vol}(\widehat{\mathcal O}) = ((\mathrm{rd}_E/2)^f)^{-1}$ and $\frac14 \log |D_E| = \frac f2 \log \mathrm{rd}_E$. The difference in the claim is $-\log\|x\|$. For $\|x - 1\| \le \frac12$,
$$
|\log \|x\|| \le |\log(1 + (x - 1))| \le \tfrac32 \|x - 1\| \le 4 \cdot 2^{-(u+1)} = \frac{2}{2^u}. \qquad \square
$$

The statement holds for every $u$ with $8f \le 2^u$. A larger $u$ gives a smaller error and needs a larger rank. The error does not depend on the discriminant, only on $f$ through the condition $8f \le 2^u$.

**Remark (Formalization).** The classical mass formula for unimodular hermitian lattices gives the mass exactly, as a product of special values of $L$-functions with local factors. The source names W. T. Gan, J. Hanke and J.-K. Yu, Duke Math. J. 107 (2001), and M. Kirschmer, Definite quadratic and hermitian forms with small class number (2016), 4.2.7 and 4.2.9. This chapter has not checked those numbers against the texts. The source form is weaker in three ways. It gives only the ratio of masses in consecutive ranks. It holds only in large rank, $j \ge 4u + 12$. It has an explicit error $2/2^u$ in place of the $L$-value factor. The field must have Weil data, so it contains a primitive root of unity of order $5040$ and has a splitting character and a self-dual rank-one lattice. The number $x$ is a choice made by `obtain` from the surjectivity of multiplication by $\mathrm{vol}(\widehat{\mathcal O})^{j+1}$. It is the density divided by this volume.

The frame mass estimate in [Poincaré series](/chapter/poincare-series/), in New/Spanning/Unfolding/FrameMass.lean, uses this estimate.
