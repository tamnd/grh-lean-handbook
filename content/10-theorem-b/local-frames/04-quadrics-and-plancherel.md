---
title: Quadrics and Plancherel
lean:
  - New/Spanning/Frames/QuadricVolumes.lean
  - New/Spanning/Frames/QuadricPlancherel.lean
decls:
  - New.Floors.Gauge.exists_isSolvedIn
  - New.Floors.sectionPoint
  - New.Floors.sectionMeasure
  - New.Floors.PlaceData.lintegral_floorQuadricMeasure_eq
  - New.Floors.Gauge.setLIntegral_sectionMeasure_le
  - New.Floors.Gauge.floorMassLe_one
  - New.Floors.Gauge.fourierSqNormLe_floorQuadricMeasure
  - New.Floors.Gauge.correlation_plancherel
  - New.Floors.Gauge.partialCorrelation_weylRatio_heisenbergElem
  - New.Floors.Gauge.parseval_heisenbergMeasure_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Quadrics and Plancherel

On floor $b$ the frame vector $f_b$ runs over a quadric: the map $\sigma \mapsto \sigma^{-1}f_b$ (`orbitPoint b σ`) carries $\theta_b$ to a measure $\rho_b$ on the quadric through $f_b$ (`floorQuadricMeasure b`, see `New.Floors.PlaceData.measurePreserving_orbitPoint`). This section proves Plancherel's formula on these quadrics. The idea is classical: a quadric is the graph of a function over most of its coordinates, and on these free coordinates the Fourier kernel $\psi(\xi h(v, y))$ is the Fourier transform of a linear space, for which Plancherel's formula holds. The work is in choosing the coordinates so that the same block serves both points of a pair.

The bound uses the space $X'$. The basis of the place datum has $\#\iota$ orthonormal vectors. The source sets aside two blocks of $2m + 2$ of them (`blockRank`), and $X'$ is the span of the other $\#\iota - 2(2m + 2)$ vectors (the index type `FreeIndex`). For a vector $y$, the source writes $y_X$ for the vector of the products of the basis vectors of $X'$ with $y$. Let $c_P \geq 1$ be the constant of Plancherel's formula at the place (`P.kernelBound`).

### Solving a quadric in a block

**Lemma (Solved in every block).** Let $\Gamma$ be a gauge and let $\rho$ be the volume of the vectors of floor at least $b$ or the measure $\rho_b$ of the quadric of floor $b$. In the coordinates of the basis of floor $b$, $\rho$ is the image of a measure $\rho_0$ such that, for every injective choice of $2m + 2$ orthonormal basis vectors (a *block*) and every $j$, $\rho_0$ is solved in the block: the other coordinates are free with the volume, and over each of their values the points of the block with all coordinates of size $j$ have mass at most $\Lambda^{(2m+2)(j+1)}$.

Lean: `New.Floors.Gauge.exists_isSolvedIn` (New/Spanning/Frames/QuadricVolumes.lean).

*Proof.* For the volume there is nothing to solve, and the bound is field 5 of the gauge. For the quadric, the gauge gives a disintegration of the volume of the block along the standard form (field 7). The equation of the quadric fixes the value of the form on the block, and the measure over each value is one of the measures of the kernel. $\square$

### Sections of the cone

For $a < \varrho$ and $c \in A$, the vector $\mathrm{sp}_a(c, n) = c\,n^{-1}e^*_a$ (`sectionPoint a c n`) is, for $n$ in the Heisenberg group of floor $a$, a point of the section $h(e_a, y) = c$ of the isotropic cone of $Y^{(a)}$.

**Definition (Section measure).** The measure $\varsigma_{a, c}$ (`sectionMeasure T a c`) on the section $h(e_a, y) = c$ is $|c|^{r}$ times the image of $\eta_a$ under $n \mapsto \mathrm{sp}_a(c, n)$, where $r = r_a = k + 1 + 2(\varrho - (a + 1))$ is the rank of $Y^{(a+1)}$.

Lean: `New.Floors.sectionMeasure` (New/Spanning/Frames/QuadricVolumes.lean). The point is `New.Floors.sectionPoint` (same file).

**Lemma (The cone by sections).** For a measurable $f \geq 0$ on $V$ and $a < \varrho$,

$$\int f\,d\rho_a = \int_A\int f(y)\,d\varsigma_{a, c}(y)\,dc.$$

Lean: `New.Floors.PlaceData.lintegral_floorQuadricMeasure_eq` (New/Spanning/Frames/QuadricVolumes.lean).

*Proof.* The measure $\theta_a = \lambda_a\ast\eta_a$ is the law of $w_a(c)^{-1}n$, where $c$ has the density $|c|^{r}$ and $n$ has the law $\eta_a$. Its image under $\sigma \mapsto \sigma^{-1}e_a$ is the law of $n^{-1}w_a(c)e_a = n^{-1}(ce^*_a)$, up to the convention for $w_a(c)$, which is $\mathrm{sp}_a(c, n)$. $\square$

**Lemma (Integration over a section).** Let $c$ be a unit, $\varphi \geq 0$ measurable on $X'$, and let $\int_{A_{(j+5)}^{X'}}\varphi \leq B$. Then

$$\int_{V_{(j)}}\varphi(y_X)\,d\varsigma_{a, c}(y) \leq |c^{-1}|^{1/2}\cdot\Lambda^{j+3}\cdot\Lambda^{99n(j+7)}\cdot B,$$

where $V_{(j)}$ is the set of the vectors of size $j$.

Lean: `New.Floors.Gauge.setLIntegral_sectionMeasure_le` (New/Spanning/Frames/QuadricVolumes.lean).

*Proof.* The source integrates over the Heisenberg group at the scale $-1/c$. The rescaling has the modulus $|c^{-1}|^{r_a + 1/2}$ (`F.floorModulus a c⁻¹`), and the power $|c|^{r_a}$ in the section measure cancels against it, which leaves $|c^{-1}|^{1/2}$. The rescaled points are vectors of the floor whose coordinates are bounded by the sizes. The coordinate along $e_a$ costs $\Lambda^{j+3}$, and the integral over the floor of $\varphi(y_X)$ costs $\Lambda^{99n(j+7)}B$ by solving in one block (`New.Floors.Gauge.setLIntegral_orthonormalPart_le`). $\square$

**Lemma (Mass of a floor).** For every $b < n$, the statement `FloorMassLe b C 1` holds with $C = \Lambda^{99\cdot 13n}\cdot\mathrm{vol}(A_{(11)})^{\#\mathrm{FreeIndex}}$. That is, for every $g$ the $\sigma$ with $\sigma g$ near at $b + 1$ have $\theta_b$-mass at most $C$.

Lean: `New.Floors.Gauge.floorMassLe_one` (New/Spanning/Frames/QuadricPlancherel.lean).

*Proof.* If $\sigma g$ is near at $b + 1$, then $\sigma^{-1}f_b$ is a short point of the quadric, and the source reduces the mass to an integral over the short points of the quadric (`New.Floors.Gauge.floorMassLe_of_chart`). Vectors of size $7$ have coordinates of size $7 + 4 = 11$ in the basis of the floor. Solving in one block with $\varphi = 1$ (`New.Floors.Gauge.setLIntegral_orthonormalPart_le`) gives $\Lambda^{99n(7+6)}$ times the volume of the free coordinates, which is at most $\mathrm{vol}(A_{(11)})^{\#\mathrm{FreeIndex}}$. $\square$

### Plancherel's formula on a quadric

The statement `FourierSqNormLe J ξ ρ' ρ S' S C` says that the kernel $\psi(\xi h(v, y))$ multiplies squared norms by at most $C$ from the functions on $(S, \rho)$ to the functions on $(S', \rho')$. That is, for every measurable $\rho$-integrable $\varphi$ that vanishes off $S$,

$$\int_{S'}\Bigl|\int\psi(\xi h(v, y))\varphi(y)\,d\rho(y)\Bigr|^2d\rho'(v) \leq C\int|\varphi|^2\,d\rho.$$

**Theorem (Plancherel on a quadric).** Let $\xi$ be a unit, $b < n$, $i, j \in \mathbb{N}$, and let $\rho$ be the volume of floor $b$ or the measure $\rho_b$. Then the kernel $\psi(\xi h(v, y))$ from the vectors $y$ of size $j$ with the measure $\rho_b$ to the vectors $v$ of size $i$ with the measure $\rho$ multiplies squared norms by at most

$$\Lambda^{99n(i+6)}\cdot\Lambda^{99n(j+6)}\cdot(c_P/|\xi|)^{\#\mathrm{FreeIndex}}.$$

Lean: `New.Floors.Gauge.fourierSqNormLe_floorQuadricMeasure` (New/Spanning/Frames/QuadricPlancherel.lean).

*Proof.* Choose two disjoint blocks, one for $v$ and one for $y$. Solve the quadric of $y$ in its block and the quadric of $v$ (if $\rho = \rho_b$) in the other block. The product $h(v, y)$ splits into a sum over $X'$, a sum over the two blocks and the coordinates of the hyperbolic part. Apply the Cauchy-Schwarz inequality in the block coordinates, whose masses are bounded by the lemma on blocks, and Plancherel's formula for the additive character in the coordinates of $X'$. Plancherel's formula gives the factor $(c_P/|\xi|)$ for each coordinate of $X'$. $\square$

**Theorem (Plancherel for a correlation).** Let $k$ be a pairing kernel at floor $b$ for $d$, let $t \in G^{(b)}$, $q$ with $t^{-1}q \in U_{<b}$, and let $qx$ have size $j$. Let $\xi$ be a unit, $v_0$ a vector, $y \in \mathsf{G}$, and $\rho$ as before. Then

$$\begin{aligned}
&\int_{V_{(i)}}\Bigl|\int\psi\bigl(\xi h(v + v_0, t\sigma^{-1}f_b)\bigr)k_{b+1}(\sigma x, \sigma y)\,d\theta_b(\sigma)\Bigr|^2d\rho(v)\\
&\qquad\leq \Lambda^{99n(i+6)}\Lambda^{99n(j+12)}\Bigl(\frac{c_P}{|\xi|}\Bigr)^{\#\mathrm{FreeIndex}}\int|k_{b+1}(\sigma x, \sigma y)|^2\,d\theta_b(\sigma).
\end{aligned}$$

Lean: `New.Floors.Gauge.correlation_plancherel` (New/Spanning/Frames/QuadricPlancherel.lean).

*Proof.* Push $\theta_b$ to the quadric by $\sigma \mapsto \sigma^{-1}f_b$. By rule 2 of a pairing kernel, the correlation is a function of $\sigma^{-1}f_b$ times a phase. By rule 5, it vanishes unless $\sigma x$ is near at $b + 1$, and then $\sigma^{-1}f_b$ has size $j + 6$ (`New.Floors.Gauge.correlation_support`). The shift $v_0$ and the element $t$ are absorbed by a change of variables. Apply the theorem on a quadric with $j + 6$ in place of $j$. $\square$

### Along a Heisenberg group

Let $n = \mathrm{he}_a(t)$ (`P.heisenbergElem a t`) be the element of the Heisenberg group of floor $a$ with parameter $t = (\omega, \beta)$, where $\omega$ is a vector of floor at least $a + 1$ and $\beta$ is skew.

**Lemma (A correlation along a Heisenberg group).** Let $j \leq a + 1$, $\varepsilon \leq 1$, let $k$ be a pairing kernel at floor $a + 1$ for $w_q^{-1}w_p$ (`weylRatio j p q`), and let $x, y \in \mathsf{G}$. Then $k_{a+1}(n^\varepsilon x, ny)$ is equal to

$$\int\psi\bigl(-\xi\,h(\omega, \sigma^{-1}f_{a+1})\bigr)k_{a+2}(\sigma x, \sigma y)\,d\theta_{a+1}(\sigma),$$

where $\xi = M^{-1}(p_a/q_a - \varepsilon)$ if $a < j$ and $\xi = M^{-1}(1 - \varepsilon)$ otherwise.

Lean: `New.Floors.Gauge.partialCorrelation_weylRatio_heisenbergElem` (New/Spanning/Frames/QuadricPlancherel.lean).

*Proof.* Write $k_{a+1}$ as an integral over floor $a + 1$ (the lemma on one floor up). The element $n$ commutes past $\sigma$ up to an element of $U_{<a+1}$, and rule 2 of a pairing kernel turns this element into a phase. The phase is $\psi$ of $M^{-1}$ times the difference of the simple root sums. Since $w_q^{-1}w_p$ scales $e_a$ by $p_a/q_a$, the difference is $(p_a/q_a - \varepsilon)h(\omega, \sigma^{-1}f_{a+1})$ (`New.Floors.Gauge.simpleRootSum_weylRatio_conj`). $\square$

**Theorem (Parseval along a Heisenberg group).** Let $a < \varrho$, let $k$ be a pairing kernel at floor $a + 1$ for $d$, let $\xi, u$ be units, $\varepsilon \in \mathbb{N}$, $C \in [0, \infty]$, $x, y \in \mathsf{G}$, $S \subseteq \mathsf{G}$, $i, j \in \mathbb{N}$ and $\Phi \geq 0$. Suppose:

1. for $s$ in the Heisenberg group $N_a$ of floor $a$, $M^{-1}(\sigma_0(dsd^{-1}) - \sigma_0(s^\varepsilon)) = \xi\sigma_0(s)$;
2. for $n \in N_a$ with $\Phi(n) \neq 0$, $n \in S$ and $\Phi(n) \leq C|k_{a+1}(n^\varepsilon x, ny)|^2$;
3. for each $n_0 \in S$ there are $t \in R^{(a+1)}\cap G^{(a)}$ and $q \in U_{<a+1}$ such that $tqx$ has size $i$ and, for each $n \in S$, some $v$ congruent to $(tn_0(tn)^{-1} - 1)e^*_a$ modulo the $e_b$ ($b < a$) has $u^{-1}v$ of size $j$.

Then

$$\int\Phi\,d\eta_a \leq C\cdot\Bigl(\frac{c_P}{|\xi u|}\Bigr)^{\#\mathrm{FreeIndex}}\cdot|u|^{r_a + 1/2}\cdot\Lambda^{100n(i+j+31)}\int|k_{a+2}(\sigma x, \sigma y)|^2\,d\theta_{a+1}(\sigma),$$

where $|u|^{r_a+1/2}$ is `F.floorModulus a u` and $r_a = k + 1 + 2(\varrho - a - 1)$ is the rank of the vector part of $N_a$.

Lean: `New.Floors.Gauge.parseval_heisenbergMeasure_le` (New/Spanning/Frames/QuadricPlancherel.lean).

*Proof.* By hypothesis 1 the correlation along $N_a$ is a Fourier transform in the next frame vector, as in the lemma above, with the frequency $\xi$. Hypothesis 3 says that $S$ lies in a ball of radius $|u|$ around each of its points, measured by the vectors $(n_0n^{-1} - 1)e^*_a$. Rescale the vector part of $N_a$ by $u$. This costs the factor $|u|^{r_a+1/2}$ of the Haar measure, and the frequency becomes $\xi u$. The theorem of Plancherel for a correlation then bounds the integral of the square, with the sizes $i$ and $j$ in the exponent of $\Lambda$. $\square$

**Remark (Formalization).** The Plancherel bounds are inequalities for integrals in $[0, \infty]$. They hold for every function, also when the right side is infinite, and they need no integrability hypothesis on the correlation. The inner integral over $\sigma$ is a Bochner integral, which Lean sets to $0$ when the integrand is not integrable; rule 4 of a pairing kernel excludes this case. The exponent $\#\mathrm{FreeIndex} = \#\iota - 2(2m + 2)$ is the rank of $X'$, not the full rank of the quadric, since the two blocks are used up by the Cauchy-Schwarz inequality.
