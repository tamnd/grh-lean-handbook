---
title: Local densities at a finite place
lean:
  - Lib/SiegelWeil/OneVector/ResidueClasses.lean
  - Lib/SiegelWeil/OneVector/ClassGaussSums.lean
  - Lib/SiegelWeil/OneVector/SemilocalDensityBounds.lean
  - Lib/SiegelWeil/OneVector/StandardQuadrics.lean
  - Lib/SiegelWeil/OneVector/FinitePlaceDensity.lean
  - Lib/General/Measure/QuadricDisintegration.lean
  - Lib/SiegelWeil/Mass.lean
decls:
  - New.Floors.IntegralPlace.latticeMultiple
  - New.Floors.IntegralPlace.residueClass
  - New.Floors.IntegralPlace.volume_residueClass
  - New.Floors.Place.IsDisintegration
  - New.Floors.IntegralPlace.isDisintegration_of_hyperbolic_basis
  - New.Floors.IntegralPlace.integral_skewMeasure_eq_toReal_lintegral
  - New.Floors.IntegralPlace.enorm_localDensity_le
  - New.Floors.IntegralPlace.classGaussSum
  - New.Floors.IntegralPlace.enorm_classGaussSum_sq_le
  - New.Floors.IntegralPlace.integral_classGaussSum
  - New.Floors.IntegralPlace.measure_residueClass_le_lintegral
  - New.idealZeta
  - New.Floors.IntegralPlace.lintegral_enorm_classGaussSum_le_idealZeta
  - New.Floors.IntegralPlace.measure_residueClass_le_idealZeta
  - New.Floors.IntegralPlace.one_add_enorm_measure_intVectors_sub_one_le
  - New.Floors.IntegralPlace.exists_kernel_isDisintegration_le
status: drafted
drafted_by: writer@claude-opus-5-5
---

## Local densities at a finite place

Siegel's formula of the previous section has a local factor at the finite places, the density `New.normDensity`. The source does not compute this factor. It bounds it. This section gives the local results that make the bound. They hold at a finite place $A$ in the sense of `IntegralPlace`. Such an $A$ can be a product of several completions, so one set of results covers all finite places at once.

### The setting

An integral place $A$ is a semilocal ring with an involution $x \mapsto \bar x$, a ring of integers $R$, an additive character $\psi$, and a Haar measure. It carries these data:

- an integral element $\tau$, `element`, with $\tau + \bar\tau = 1$;
- a unit $\delta$, `skewUnit`, with integral inverse and $\bar\delta = -\delta$;
- a measure $\nu$, `skewMeasure`, on the skew elements $b$, those with $\bar b = -b$;
- the modulus $|x|$, `modulus`, the factor by which multiplication by $x$ scales Haar measure.

The map $(a, b) \mapsto \tau\delta^{-1}a + b$ carries $\nu \otimes \nu$ to Haar measure. The character $\psi$ is self-dual for $R$. In most results it is also trivial on traces:

$$
\psi(x + \bar x) = 1 \quad \text{for all } x \in A.
$$

A hermitian matrix $J$ over $A$ gives the form $h(x, x) = \bar x^{\mathsf T} J x$ on $A^\kappa$. The form is unimodular, `IsUnimodular R J`, if $J$ is hermitian and lies in $\mathrm{GL}_\kappa(R)$. Let $L = R^\kappa$ be the lattice of integral vectors.

### Classes modulo a lattice

For a unit $g$ of $A$, put $gL$ for the image of $L$ under multiplication by $g$. For a vector $x_0$, the class of $x_0$ modulo $gL$ is $x_0 + gL$.

**Theorem (Volume of a class).** For a unit $g$ and a vector $x_0$, the class $x_0 + gL$ is open and compact, and
$$
\mathrm{vol}(x_0 + gL) = |g|^{\#\kappa}.
$$
Lean: `New.Floors.IntegralPlace.volume_residueClass`, `New.Floors.IntegralPlace.residueClass`, `New.Floors.IntegralPlace.latticeMultiple`, `New.Floors.IntegralPlace.volume_latticeMultiple`, `New.Floors.IntegralPlace.isOpen_residueClass`, `New.Floors.IntegralPlace.isCompact_residueClass` (Lib/SiegelWeil/OneVector/ResidueClasses.lean)

*Proof.* The volume of $\{x : g^{-1}x \in R\}$ is $|g|$. The lattice $gL$ is a product of these sets, one for each coordinate. A translation preserves Haar measure. $\square$

### Measures on quadrics

**Definition (Disintegration).** Let $\mu$ be a measure on $A^\kappa$ and $J$ hermitian. A family $l$ of measures $l_b$ on $A^\kappa$, indexed by the skew $b$, disintegrates $\mu$ along $J$ if these two conditions hold.

1. For continuous $f \ge 0$ of compact support, $b \mapsto \int f \, dl_b$ is continuous and finite.
2. For measurable $f \ge 0$ on $A \times A^\kappa$,
$$
\int f(h(x, x), x) \, d\mu(x) = \int \int f(\delta^{-1}b, x) \, dl_b(x) \, d\nu(b).
$$

Lean: `New.Floors.Place.IsDisintegration` (Lib/General/Measure/QuadricDisintegration.lean)

The measure $l_t$ lives on the quadric $h(x, x) = \delta^{-1}t$. The index $t$ is skew, so $\delta^{-1}t$ is hermitian. The family is a choice of fiber measures. Condition 2 fixes $l_t$ only for $\nu$-almost every $t$. Condition 1 then fixes it for every $t$, on continuous functions of compact support.

For the standard form there is an explicit family.

**Theorem (The standard form disintegrates).** Let $\#\kappa \ge 2$. There is a matrix $B$ with $B^{\mathsf H}B$ equal to a hyperbolic pair followed by an identity matrix. For such a $B$, the images under $x \mapsto Bx$ of the measures `quadricMeasure 1 b` disintegrate the volume along $J = 1$.
Lean: `New.Floors.IntegralPlace.isDisintegration_of_hyperbolic_basis`, `New.Floors.IntegralPlace.exists_hyperbolic_basis`, `New.Floors.Place.isDisintegration_map_quadricMeasure`, `New.Floors.Place.quadricMeasure` (Lib/SiegelWeil/OneVector/StandardQuadrics.lean; Lib/General/Measure/QuadricDisintegration.lean)

*Proof.* Take $c$ with $\bar c c = -1$. From two orthonormal vectors $x$ and $y$ and the element $\tau$ the proof builds a hyperbolic pair. The rest of the standard basis gives the identity block. On a hyperbolic plane plus a form, `flatChart` gives the points of a quadric by explicit coordinates, and `quadricMeasure` is the image of a product measure under it. The general disintegration lemma for this measure applies, because the determinant of $J = 1$ has modulus one. $\square$

### Fourier inversion

The density of $f$ at the level $\delta^{-1}t$ is a Fourier integral over the skew frequencies:
$$
D_f(t) = \int_b \int_x f(x) \, \psi\bigl(\tau b (h(x, x) - \delta^{-1}t)\bigr) \, dx \, d\nu(b).
$$
The next theorem says that this integral is the mass of $f$ on the quadric.

**Theorem (Fourier inversion for local densities).** Let $l$ disintegrate the volume along a hermitian $J$, let $\psi$ be trivial on traces, let $f \ge 0$ be continuous of compact support, and let $t$ be skew. If the inner integral is integrable in $b$ for $\nu$, then
$$
D_f(t) = \Bigl(\int f \, dl_t\Bigr)_{\mathbb{R}}.
$$
Lean: `New.Floors.IntegralPlace.integral_skewMeasure_eq_toReal_lintegral`, `New.Floors.IntegralPlace.psi_skew_eq_one_iff`, `New.Floors.IntegralPlace.setIntegral_eq_slab`, `New.Floors.Place.IsDisintegration.setLIntegral_slab`, `New.Floors.IntegralPlace.tendsto_average_skew` (Lib/SiegelWeil/OneVector/FinitePlaceDensity.lean)

*Proof.* Cut the frequencies to the set $C_y$ of the skew $b$ with $y\bar y b \in R$, for a unit $y$.

*Step 1: orthogonality.* Let $u$ be a hermitian unit and $y'$ hermitian. The character $b \mapsto \psi(\tau b y')$ is trivial on the skew $b$ with $ub \in R$ if and only if $u^{-1}\delta y' \in R$. This follows from self-duality and the trace condition. So the integral over $C_y$ is $\nu(C_y)$ times the mass of $f$ on a slab, the set of $x$ where $(y\bar y)^{-1}\delta(h(x, x) - \delta^{-1}t)$ is integral.

*Step 2: the slab.* Condition 2 of the disintegration turns the mass on the slab into the integral of $\int f \, dl_{t + b}$ over the skew $b$ in a ball about zero.

*Step 3: the limit.* The product in Steps 1 and 2 is a mean of $b \mapsto \int f \, dl_b$ over a ball about $t$. This function is continuous by condition 1. So the mean tends to its value at $t$ as $y$ tends to zero. Units are dense in $A$, so the limit along units exists.

*Step 4.* The sets $C_y$ cover the skew elements as $y$ tends to zero. The integrand is integrable, so the cut integrals tend to the full integral. The two limits agree. $\square$

**Theorem (The density is at most the mass).** Under the same hypotheses, without integrability,
$$
\|D_f(t)\| \le \int f \, dl_t.
$$
Lean: `New.Floors.IntegralPlace.enorm_localDensity_le` (Lib/SiegelWeil/OneVector/FinitePlaceDensity.lean)

*Proof.* If the inner integral is integrable, this is the previous theorem. If not, the Bochner integral $D_f(t)$ is $0$, and the bound is trivial. $\square$

**Remark (Formalization).** Classically the local density is a limit. At a prime $\mathfrak p$ it is the limit over $k$ of the volume of the $x \in L$ with $h(x, x) \in \delta^{-1}t + \mathfrak p^k$, divided by the volume of $\delta^{-1}t + \mathfrak p^k$. The source names C. L. Siegel, Ann. of Math. 36 (1935), for the classical theory. This chapter has not checked a section number there, so it gives none. The source has two other forms. The first is the mass $\int f \, dl_t$ for a fixed disintegration $l$. The second is the Fourier integral $D_f(t)$. Step 3 of the proof above is the classical limit, with balls $y\bar y R$ in place of $\mathfrak p^k$. The Fourier integral has a junk value. When the inner integral is not integrable in $b$, Lean's integral gives $D_f(t) = 0$. The bound `enorm_localDensity_le` is then true for a trivial reason. The equality needs integrability as a hypothesis. The mass $\int f \, dl_t$ is stated for a given family $l$. The results of this section hold for every family that disintegrates the volume.

### Gauss sums of classes

**Definition (Gauss sum of a class).** For a unit $g$, a vector $x_0$, a level $\alpha \in A$ and a frequency $b$,
$$
G(g, x_0, \alpha, b) = \int_{y \in gL} \psi\bigl(\tau b (h(x_0 + y, x_0 + y) - \alpha)\bigr) \, dy.
$$
Lean: `New.Floors.IntegralPlace.classGaussSum`, `New.Floors.IntegralPlace.psi_mul_trace` (Lib/SiegelWeil/OneVector/ClassGaussSums.lean)

For skew $b$ and $\psi$ trivial on traces, `psi_mul_trace` gives $\psi(\tau b(s + \bar s)) = \psi(bs)$. This lets the proofs remove $\tau$ from bilinear terms.

**Theorem (Weyl differencing).** Let $J$ be unimodular, $\psi$ trivial on traces and $b$ skew. Let $w$ be a unit such that $w^{-1}c \in R$ for every $c \in R$ with $g\bar g b c \in R$. Then
$$
\|G(g, x_0, \alpha, b)\|^2 \le |g|^{\#\kappa} \cdot (|g| \, |w|)^{\#\kappa}.
$$
Lean: `New.Floors.IntegralPlace.enorm_classGaussSum_sq_le` (Lib/SiegelWeil/OneVector/ClassGaussSums.lean)

*Proof.* Write $M = gL$. The square of $\|G\|$ is the integral over $d \in M$ of the autocorrelation of the integrand at the shift $d$. Expand $h(x + d, x + d) - h(x, x)$. The term $h(d, d)$ gives a phase that does not depend on $x$. The cross term is a trace, so `psi_mul_trace` turns it into a character of $M$ in the variable $x$. Its integral over $M$ is $\mathrm{vol}(M)$ if the character is trivial and $0$ if not. The hypothesis on $w$ shows that the character is trivial only for $d$ in $N = gwL$. So $\|G\|^2 \le \mathrm{vol}(M)\,\mathrm{vol}(N)$, and both volumes come from the volume of a class. $\square$

**Theorem (Gauss sums give the mass of a class).** Let $l$ disintegrate the volume along a hermitian $J$, and let $\psi$ be trivial on traces.

1. If the Gauss sums at $\alpha = \delta^{-1}t$ are integrable in $b$, then
$$
\int G(g, x_0, \delta^{-1}t, b) \, d\nu(b) = l_t(x_0 + gL)_{\mathbb{R}}.
$$
2. Always,
$$
l_t(x_0 + gL) \le \int \|G(g, x_0, \delta^{-1}t, b)\| \, d\nu(b).
$$

Lean: `New.Floors.IntegralPlace.integral_classGaussSum`, `New.Floors.IntegralPlace.measure_residueClass_le_lintegral`, `New.Floors.IntegralPlace.integrable_classGaussSum` (Lib/SiegelWeil/OneVector/ClassGaussSums.lean)

*Proof.* The class is open and compact, so its indicator is continuous of compact support. A translation by $x_0$ turns the Gauss sum into the inner integral of Fourier inversion for this indicator. This gives part 1. For part 2, if the right side is infinite there is nothing to prove. If it is finite, the Gauss sums are integrable by `integrable_classGaussSum`, and part 1 gives the bound. $\square$

### The ideal zeta bound

The Gauss sum bound depends on $b$ through the ideal of the $c \in R$ with $g\bar g b c \in R$. The source sums over these ideals with a zeta function of $R$.

**Definition (Ideal zeta sum).** For a natural number $s$,
$$
\zeta_R(s) = \sum_{I} [R : I]^{-s} \in [0, \infty],
$$
over the ideals $I$ of $R$ of finite index.
Lean: `New.idealZeta`, `New.lintegral_le_idealZeta_mul` (Lib/SiegelWeil/Mass.lean)

The lemma `lintegral_le_idealZeta_mul` is the summation step. Let $\zeta_R(\mu) \le 2$. If almost every point of $s$ lies in a set $S_I$ with $[R : I]^\mu \, f(x) \, \rho(S_I) \le V$, then $\int_s f \, d\rho \le \zeta_R(\mu) V$.

**Theorem (The Gauss sums of a class have small integral).** Let $\zeta_R(\mu) \le 2$, let $J$ be unimodular of rank $\#\kappa \ge 2\mu + 1$, and let $\psi$ be trivial on traces. Then
$$
\int \|G(g, x_0, \alpha, b)\| \, d\nu(b) \le \zeta_R(\mu) \cdot |g|^{-1} \cdot |g|^{\#\kappa}.
$$
Lean: `New.Floors.IntegralPlace.lintegral_enorm_classGaussSum_le_idealZeta`, `New.Floors.IntegralPlace.skewMeasure_setOf_mul_mem_sq_le`, `New.Floors.IntegralPlace.exists_unit_sub_mem` (Lib/SiegelWeil/OneVector/SemilocalDensityBounds.lean)

*Proof.* For each $b$, `exists_unit_sub_mem` gives a unit $\eta$ such that $\eta^{-1}$ generates the ideal $I$ of the $c \in R$ with $g\bar g b c \in R$. No uniformizer is needed. Sort the $b$ by $I$, and let $S_I$ be the set of the $b$ that send $I$ into $R$ in this way. With $w$ a generator of $I$, Weyl differencing saves $[R : I]^{\#\kappa}$ in the square of $\|G\|$. By `skewMeasure_setOf_mul_mem_sq_le`, the square of $\nu(S_I)$ is at most $[R : I] \, |g|^{-2}$. Take square roots and multiply. The exponent of $[R : I]$ is at most $-\mu$, because $\#\kappa \ge 2\mu + 1$. The summation lemma gives the bound. $\square$

**Theorem (Mass of a class on a quadric).** Let $\zeta_R(\mu) \le 2$, let $J$ be unimodular of rank $\#\kappa \ge 2\mu + 1$, let $l$ disintegrate the volume along $J$, and let $\psi$ be trivial on traces. For every unit $g$, vector $x_0$ and skew $t$,
$$
l_t(x_0 + gL) \le \zeta_R(\mu) \, |g|^{-1} \, \mathrm{vol}(x_0 + gL).
$$
Lean: `New.Floors.IntegralPlace.measure_residueClass_le_idealZeta` (Lib/SiegelWeil/OneVector/SemilocalDensityBounds.lean)

*Proof.* Combine part 2 of the previous Gauss sum theorem, the integral bound, and the volume of a class. $\square$

### The lattice on an integral quadric

At $g = 1$ and $x_0 = 0$ the class is $L$ itself. For integral $\alpha$ and integral $b$ the integrand of the Gauss sum is $1$ on $L$, by self-duality. So
$$
G(1, 0, \alpha, b) = \mathrm{vol}(L) = 1.
$$
Lean: `New.Floors.IntegralPlace.classGaussSum_one_zero_eq_one` (Lib/SiegelWeil/OneVector/SemilocalDensityBounds.lean)

**Theorem (Mass of the lattice).** Let $\zeta_R(\mu) \le 2$, let $J$ be unimodular of rank $\#\kappa \ge 2\mu + 1$, let $l$ disintegrate the volume along $J$, and let $\psi$ be trivial on traces. For skew $t$ with $t \in R$,
$$
1 + \bigl\| l_t(L)_{\mathbb{R}} - 1 \bigr\| \le \zeta_R(\mu).
$$
Lean: `New.Floors.IntegralPlace.one_add_enorm_measure_intVectors_sub_one_le` (Lib/SiegelWeil/OneVector/SemilocalDensityBounds.lean)

*Proof.* At $g = 1$ the integral bound for Gauss sums gives $\int \|G(1, 0, \alpha, b)\| \, d\nu(b) \le \zeta_R(\mu)$, with $\alpha = \delta^{-1}t$. This is finite, so the Gauss sums are integrable, and their integral is the mass of $L$. Split the integral into the set $S$ of the integral $b$ and its complement. The set $S$ has measure $1$, and on it the Gauss sum is $1$, because $\alpha$ is integral. So the integral over $S$ is $1$, and the integral over the complement is $l_t(L) - 1$. The norm of each part is at most the integral of $\|G\|$ over that part. Add the two bounds. $\square$

The bound is in the extended reals. Here $\zeta_R(\mu) \le 2$ is a hypothesis, so the right side is finite. When $\zeta_R(\mu)$ is close to $1$, the mass of $L$ on the quadric is close to $1$.

### Disintegrations with a mass bound

The last result packages the above for the standard form. It is the form that the frame computations of [Volume 10](/chapter/finite-densities/) use.

**Theorem (A disintegration with bounded masses).** Let $\psi$ be trivial on traces, let $\zeta_R(\mu) \le 2$, and let $\#\kappa = r + 1$ with $2\mu + 1 \le r$. There is an s-finite kernel $l$ from the skew elements to $A^\kappa$ that disintegrates the volume along $J = 1$, such that for every skew $\beta$ and every unit $u$,
$$
l_\beta\bigl(\{y : u y_i \in R \text{ for all } i\}\bigr) \le \zeta_R(\mu) \, |u|^{-r}.
$$
Lean: `New.Floors.IntegralPlace.exists_kernel_isDisintegration_le`, `New.Floors.card_eq_card_pair_sum` (Lib/SiegelWeil/OneVector/StandardQuadrics.lean)

*Proof.* Take the basis $B$ of the standard form that begins with a hyperbolic pair. The kernel is the image of the parameter measure under the flat chart followed by $B$. This is a kernel, so it is s-finite, and it equals the family of the theorem on the standard form. So it is a disintegration. The box of the $y$ with $uy$ integral is the class of $0$ modulo $u^{-1}L$. Its volume is $|u|^{-(r+1)}$. The mass of a class on a quadric, at $g = u^{-1}$, gives the factor $\zeta_R(\mu)\,|u^{-1}|^{-1} = \zeta_R(\mu)\,|u|$. The product is $\zeta_R(\mu)\,|u|^{-r}$. $\square$

**Remark (Formalization).** The kernel $l$ is a choice made by an existential statement. Any $l$ with the stated properties serves in the uses. The rank hypothesis is $2\mu + 1 \le r$ with $\#\kappa = r + 1$. So the rank is at least $2\mu + 2$. The mass of a class needs only $2\mu + 1$, so the hypothesis is one stronger than the proof uses. The bound is one-sided. It gives no lower bound for the mass of the box.
