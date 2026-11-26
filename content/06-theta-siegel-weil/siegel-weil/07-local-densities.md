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

The source does not compute the finite factor `New.normDensity` of Siegel's formula. It bounds it. This section gives the local results for the bound, at a finite place $A$ in the sense of `IntegralPlace`. Such an $A$ can be a product of several completions, so the results cover all finite places at once.

### The setting

An integral place $A$ is a semilocal ring with an involution $x \mapsto \bar x$, a ring of integers $R$, an additive character $\psi$, a Haar measure, and:

- an integral element $\tau$, `element`, with $\tau + \bar\tau = 1$;
- a unit $\delta$, `skewUnit`, with integral inverse and $\bar\delta = -\delta$;
- a measure $\nu$, `skewMeasure`, on the skew elements $b$, those with $\bar b = -b$;
- the modulus $|x|$, `modulus`, the factor by which multiplication by $x$ scales Haar measure.

The map $(a, b) \mapsto \tau\delta^{-1}a + b$ carries $\nu \otimes \nu$ to Haar measure, and $\psi$ is self-dual for $R$. Most results ask that $\psi$ be trivial on traces:

$$
\psi(x + \bar x) = 1 \quad \text{for all } x \in A.
$$

A hermitian $J$ gives the form $h(x, x) = \bar x^{\mathsf T} J x$ on $A^\kappa$. It is unimodular, `IsUnimodular R J`, if $J \in \mathrm{GL}_\kappa(R)$. Let $L = R^\kappa$.

### Classes modulo a lattice

**Theorem (Volume of a class).** For a unit $g$ of $A$ and a vector $x_0$, the class $x_0 + gL$ is open and compact, and
$$
\mathrm{vol}(x_0 + gL) = |g|^{\#\kappa}.
$$
Lean: `New.Floors.IntegralPlace.volume_residueClass`, `New.Floors.IntegralPlace.residueClass`, `New.Floors.IntegralPlace.latticeMultiple` (Lib/SiegelWeil/OneVector/ResidueClasses.lean)

*Proof.* $gL$ is a product of $\#\kappa$ copies of $gR$, of volume $|g|$. $\square$

### Measures on quadrics

**Definition (Disintegration).** Let $\mu$ be a measure on $A^\kappa$ and $J$ hermitian. A family of measures $l_b$ on $A^\kappa$, for skew $b$, disintegrates $\mu$ along $J$ if:

1. For continuous $f \ge 0$ of compact support, $b \mapsto \int f \, dl_b$ is continuous and finite.
2. For measurable $f \ge 0$ on $A \times A^\kappa$,
$$
\int f(h(x, x), x) \, d\mu(x) = \int \int f(\delta^{-1}b, x) \, dl_b(x) \, d\nu(b).
$$

Lean: `New.Floors.Place.IsDisintegration` (Lib/General/Measure/QuadricDisintegration.lean)

The measure $l_t$ lives on the quadric $h(x, x) = \delta^{-1}t$.

**Theorem (The standard form disintegrates).** Let $\#\kappa \ge 2$. There is a matrix $B$ with $B^{\mathsf H}B$ equal to a hyperbolic pair followed by an identity matrix. For such a $B$, the images under $x \mapsto Bx$ of the measures `quadricMeasure 1 b` disintegrate the volume along $J = 1$.
Lean: `New.Floors.IntegralPlace.isDisintegration_of_hyperbolic_basis`, `New.Floors.IntegralPlace.exists_hyperbolic_basis`, `New.Floors.Place.isDisintegration_map_quadricMeasure`, `New.Floors.Place.quadricMeasure` (Lib/SiegelWeil/OneVector/StandardQuadrics.lean; Lib/General/Measure/QuadricDisintegration.lean)

*Proof.* Two standard basis vectors and $\tau$ give a hyperbolic pair. On a hyperbolic plane plus a form, `quadricMeasure` is the image of a product measure under explicit coordinates of the quadric, and it disintegrates the volume because $\det J = 1$ has modulus one. $\square$

### Fourier inversion

The density of $f$ at the level $\delta^{-1}t$ is a Fourier integral over the skew frequencies:
$$
D_f(t) = \int_b \int_x f(x) \, \psi\bigl(\tau b (h(x, x) - \delta^{-1}t)\bigr) \, dx \, d\nu(b).
$$
**Theorem (Fourier inversion for local densities).** Let $l$ disintegrate the volume along a hermitian $J$, let $\psi$ be trivial on traces, let $f \ge 0$ be continuous of compact support, and let $t$ be skew. If the inner integral is integrable in $b$ for $\nu$, then
$$
D_f(t) = \Bigl(\int f \, dl_t\Bigr)_{\mathbb{R}}.
$$
Lean: `New.Floors.IntegralPlace.integral_skewMeasure_eq_toReal_lintegral` (Lib/SiegelWeil/OneVector/FinitePlaceDensity.lean)

*Proof.* Cut the frequencies to the set $C_y$ of the skew $b$ with $y\bar y b \in R$, for a unit $y$. By self-duality and the trace condition, the cut integral is $\nu(C_y)$ times the mass of $f$ on a slab around the quadric. Condition 2 turns this into a mean of the continuous function $b \mapsto \int f \, dl_b$ over a ball about $t$, which tends to $\int f\,dl_t$ as $y \to 0$. By integrability the cut integrals tend to $D_f(t)$. $\square$

**Theorem (The density is at most the mass).** Under the same hypotheses, without integrability,
$$
\|D_f(t)\| \le \int f \, dl_t.
$$
Lean: `New.Floors.IntegralPlace.enorm_localDensity_le` (Lib/SiegelWeil/OneVector/FinitePlaceDensity.lean)

*Proof.* Use the previous theorem, or the junk value $D_f(t) = 0$. $\square$

**Remark (Formalization).** Classically the local density at $\mathfrak p$ is the limit over $k$ of the volume of the $x \in L$ with $h(x, x) \in \delta^{-1}t + \mathfrak p^k$, divided by the volume of $\delta^{-1}t + \mathfrak p^k$ (Siegel, Ann. of Math. 36 (1935)). The source uses instead the mass $\int f \, dl_t$ for a given disintegration $l$, and the Fourier integral $D_f(t)$. The limit in the proof above is the classical limit, with $y\bar y R$ in place of $\mathfrak p^k$. When the inner integral is not integrable in $b$, Lean gives $D_f(t) = 0$, so the bound holds for a trivial reason and the equality needs integrability as a hypothesis. 

### Gauss sums of classes

**Definition (Gauss sum of a class).** For a unit $g$, a vector $x_0$, a level $\alpha \in A$ and a frequency $b$,
$$
G(g, x_0, \alpha, b) = \int_{y \in gL} \psi\bigl(\tau b (h(x_0 + y, x_0 + y) - \alpha)\bigr) \, dy.
$$
Lean: `New.Floors.IntegralPlace.classGaussSum`, `New.Floors.IntegralPlace.psi_mul_trace` (Lib/SiegelWeil/OneVector/ClassGaussSums.lean)

For skew $b$ and $\psi$ trivial on traces, `psi_mul_trace` gives $\psi(\tau b(s + \bar s)) = \psi(bs)$.

**Theorem (Weyl differencing).** Let $J$ be unimodular, $\psi$ trivial on traces and $b$ skew. Let $w$ be a unit such that $w^{-1}c \in R$ for every $c \in R$ with $g\bar g b c \in R$. Then
$$
\|G(g, x_0, \alpha, b)\|^2 \le |g|^{\#\kappa} \cdot (|g| \, |w|)^{\#\kappa}.
$$
Lean: `New.Floors.IntegralPlace.enorm_classGaussSum_sq_le` (Lib/SiegelWeil/OneVector/ClassGaussSums.lean)

*Proof.* Write $\|G\|^2$ as the integral over shifts $d \in M = gL$ of the autocorrelation of the integrand. By `psi_mul_trace` the cross term of $h(x + d, x + d) - h(x, x)$ is a character of $M$ in $x$, and by the hypothesis on $w$ it is trivial only for $d \in gwL$. So $\|G\|^2 \le \mathrm{vol}(M)\,\mathrm{vol}(gwL)$. $\square$

**Theorem (Gauss sums give the mass of a class).** Let $l$ disintegrate the volume along a hermitian $J$, with $\psi$ trivial on traces.

1. If the Gauss sums at $\alpha = \delta^{-1}t$ are integrable in $b$, then
$$
\int G(g, x_0, \delta^{-1}t, b) \, d\nu(b) = l_t(x_0 + gL)_{\mathbb{R}}.
$$
2. Always,
$$
l_t(x_0 + gL) \le \int \|G(g, x_0, \delta^{-1}t, b)\| \, d\nu(b).
$$

Lean: `New.Floors.IntegralPlace.integral_classGaussSum`, `New.Floors.IntegralPlace.measure_residueClass_le_lintegral`, `New.Floors.IntegralPlace.integrable_classGaussSum` (Lib/SiegelWeil/OneVector/ClassGaussSums.lean)

*Proof.* The indicator of the class is continuous of compact support, so part 1 is Fourier inversion. For part 2, if the right side is finite, the Gauss sums are integrable by `integrable_classGaussSum`, and part 1 applies. $\square$

### The ideal zeta bound

**Definition (Ideal zeta sum).** For a natural number $s$,
$$
\zeta_R(s) = \sum_{I} [R : I]^{-s} \in [0, \infty],
$$
over the ideals $I$ of $R$ of finite index.
Lean: `New.idealZeta`, `New.lintegral_le_idealZeta_mul` (Lib/SiegelWeil/Mass.lean)

The summation step `lintegral_le_idealZeta_mul` says: if $\zeta_R(\mu) \le 2$ and almost every point of $s$ lies in a set $S_I$ with $[R : I]^\mu \, f(x) \, \rho(S_I) \le V$, then $\int_s f \, d\rho \le \zeta_R(\mu) V$.

**Theorem (The Gauss sums of a class have small integral).** Let $\zeta_R(\mu) \le 2$, let $J$ be unimodular of rank $\#\kappa \ge 2\mu + 1$, and let $\psi$ be trivial on traces. Then
$$
\int \|G(g, x_0, \alpha, b)\| \, d\nu(b) \le \zeta_R(\mu) \cdot |g|^{-1} \cdot |g|^{\#\kappa}.
$$
Lean: `New.Floors.IntegralPlace.lintegral_enorm_classGaussSum_le_idealZeta`, `New.Floors.IntegralPlace.skewMeasure_setOf_mul_mem_sq_le`, `New.Floors.IntegralPlace.exists_unit_sub_mem` (Lib/SiegelWeil/OneVector/SemilocalDensityBounds.lean)

*Proof.* Sort the $b$ by the ideal $I$ of the $c \in R$ with $g\bar g b c \in R$, which has a unit generator by `exists_unit_sub_mem`. Weyl differencing with $w$ a generator of $I$ saves $[R : I]^{\#\kappa}$ in $\|G\|^2$, and $\nu(S_I)^2 \le [R : I] \, |g|^{-2}$ by `skewMeasure_setOf_mul_mem_sq_le`. Since $\#\kappa \ge 2\mu + 1$, the exponent of $[R : I]$ is at most $-\mu$, and the summation step ends the proof. $\square$

**Theorem (Mass of a class on a quadric).** Let $\zeta_R(\mu) \le 2$, let $J$ be unimodular of rank $\#\kappa \ge 2\mu + 1$, let $l$ disintegrate the volume along $J$, and let $\psi$ be trivial on traces. For every unit $g$, vector $x_0$ and skew $t$,
$$
l_t(x_0 + gL) \le \zeta_R(\mu) \, |g|^{-1} \, \mathrm{vol}(x_0 + gL).
$$
Lean: `New.Floors.IntegralPlace.measure_residueClass_le_idealZeta` (Lib/SiegelWeil/OneVector/SemilocalDensityBounds.lean)

*Proof.* Combine part 2 above with the integral bound and the volume of a class. $\square$

### The lattice on an integral quadric

For integral $\alpha$ and $b$, self-duality gives
$$
G(1, 0, \alpha, b) = \mathrm{vol}(L) = 1.
$$
Lean: `New.Floors.IntegralPlace.classGaussSum_one_zero_eq_one` (Lib/SiegelWeil/OneVector/SemilocalDensityBounds.lean)

**Theorem (Mass of the lattice).** Let $\zeta_R(\mu) \le 2$, let $J$ be unimodular of rank $\#\kappa \ge 2\mu + 1$, let $l$ disintegrate the volume along $J$, and let $\psi$ be trivial on traces. For skew $t$ with $t \in R$,
$$
1 + \bigl\| l_t(L)_{\mathbb{R}} - 1 \bigr\| \le \zeta_R(\mu).
$$
Lean: `New.Floors.IntegralPlace.one_add_enorm_measure_intVectors_sub_one_le` (Lib/SiegelWeil/OneVector/SemilocalDensityBounds.lean)

*Proof.* At $g = 1$, $\int \|G(1, 0, \delta^{-1}t, b)\| \, d\nu(b) \le \zeta_R(\mu)$, so the Gauss sums are integrable with integral $l_t(L)$. The integral $b$ have measure $1$ and Gauss sum $1$, so the rest of the integral is $l_t(L) - 1$, of norm at most the rest of the integral of $\|G\|$. $\square$

### Disintegrations with a mass bound

The frame computations of [Volume 10](/chapter/finite-densities/) use the following form for the standard space.

**Theorem (A disintegration with bounded masses).** Let $\psi$ be trivial on traces, let $\zeta_R(\mu) \le 2$, and let $\#\kappa = r + 1$ with $2\mu + 1 \le r$. There is an s-finite kernel $l$ from the skew elements to $A^\kappa$ that disintegrates the volume along $J = 1$, such that for every skew $\beta$ and every unit $u$,
$$
l_\beta\bigl(\{y : u y_i \in R \text{ for all } i\}\bigr) \le \zeta_R(\mu) \, |u|^{-r}.
$$
Lean: `New.Floors.IntegralPlace.exists_kernel_isDisintegration_le`, `New.Floors.card_eq_card_pair_sum` (Lib/SiegelWeil/OneVector/StandardQuadrics.lean)

*Proof.* Take the kernel of the theorem on the standard form. The box is the class of $0$ modulo $u^{-1}L$, of volume $|u|^{-(r+1)}$, and the mass of a class at $g = u^{-1}$ gives the factor $\zeta_R(\mu)\,|u|$. $\square$

**Remark (Formalization).** The kernel $l$ is given by an existential statement, and any such $l$ serves. The rank hypothesis $2\mu + 1 \le r$ with $\#\kappa = r + 1$ is one stronger than the mass of a class needs.
