---
title: The top floor
lean:
  - New/Spanning/Frames/FiberMeasures.lean
  - New/Spanning/Frames/TopCorrelation.lean
  - New/Spanning/Frames/TopFloor.lean
decls:
  - New.Floors.Place.normFiberMeasure
  - New.Floors.IntegralPlace.isDisintegration_normFiberMeasure
  - New.Floors.HyperbolicBasis.integral_floorQuadricMeasure_top
  - New.Floors.PlaceData.scaledOrbitalIntegral
  - New.Floors.PlaceData.unfoldedPairing
  - New.Floors.IntegralPlace.IsLargeLatticeData.inner_scaledOrbitalIntegral
  - New.Floors.IntegralPlace.IsLargeLatticeData.floorForm_top_eq_integral
  - New.Floors.PlaceData.fiberPairing
  - New.Floors.PlaceData.fiberPairing_orbitPoint
  - New.Floors.PlaceData.headSumNormSq_nonneg
  - New.Floors.IntegralPlace.IsLargeLatticeData.sum_fiberPairing_nonneg
  - New.Floors.IntegralPlace.IsLargeLatticeData.floorForm_top_eq_integral_floorQuadric
  - New.Floors.PlaceData.lastEntryDensity
  - New.Floors.IntegralPlace.IsLargeLatticeData.integral_lastEntryDensity
  - New.Floors.IntegralPlace.IsLargeLatticeData.continuous_lastEntryDensity
  - New.Floors.IntegralPlace.IsLargeLatticeData.sum_lastEntryDensity_nonneg
  - New.Floors.IntegralPlace.IsLargeLatticeData.sum_lastEntryDensity_nonneg_and_eq_inv_mul_lintegral
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The top floor

On the top floor $j = \varrho$ the main term needs the form itself, not a bound. This section writes it as the Fourier transform in the last entry $t$ of a density, and proves that the density is continuous and of positive type.

The model is the circle method: the vectors of norm $-N$ with last coordinate $t$ form a sphere in the other coordinates, and integrating $\psi(\xi t)$ over $t$ gives back the whole quadric. Here the vectors are $e = l^{-1}z$ for $l$ in the floor group $G^{(\varrho)}$, $z$ is the last frame vector, of norm $-N$, and the middle space is $A^\kappa \oplus Az$ with the standard form on $A^\kappa$ (`latticeMiddleGram`).

### Fibre measures of a sphere

**Definition (Fibre measures).** The fibre measures $dx/d\langle x, x\rangle$ of the standard form on $A^\kappa$ are a family $b \mapsto \nu_b$ that disintegrates the volume along $x \mapsto x^*x$ ([fibre measures and hermitian quadrics](/chapter/congruence-subgroups/#fibre-measures-and-hermitian-quadrics)), if one exists; otherwise an arbitrary family.

Lean: `New.Floors.Place.normFiberMeasure` (New/Spanning/Frames/FiberMeasures.lean).

**Remark (Formalization).** The family is `Classical.epsilon` of the property of being a disintegration. A disintegration is unique (`New.Floors.Place.IsDisintegration.unique`), so the choice matters only when none exists. The next lemma excludes this for $\#\kappa \ge 2$.

**Lemma (The fibre measures disintegrate).** At a finite place with $\#\kappa \ge 2$, $\nu$ is a disintegration of the volume of $A^\kappa$ along $x \mapsto x^*x$.

Lean: `New.Floors.IntegralPlace.isDisintegration_normFiberMeasure` (New/Spanning/Frames/FiberMeasures.lean).

*Proof.* For $\#\kappa \ge 2$ the standard form has a hyperbolic basis $B$. The images under $B$ of the quadric measures of its flat chart disintegrate the volume. So a disintegration exists, and `Classical.epsilon_spec` gives that $\nu$ is one. $\square$

**Theorem (Slicing the top quadric).** Let $\pi$ be a unit with $\pi\bar\pi = N$, $\#\kappa \ge 2$, and $f$ continuous with compact support on the whole space. For $t \in A$ let $\alpha_t = t\bar t/N - N$ and $v_t(x) = x - N^{-1}tz$. Then $t \mapsto |\pi|^{-1}\int f(v_t(x))\,d\nu_{\delta\alpha_t}(x)$ is integrable, and

$$\int_A|\pi|^{-1}\int f(v_t(x))\,d\nu_{\delta\alpha_t}(x)\,dt = \int f\,d\theta_{\mathrm{top}},$$

where $\theta_{\mathrm{top}}$ is the measure of the top quadric (`floorQuadricMeasure`) and $\delta$ the skew unit of the place.

Lean: `New.Floors.HyperbolicBasis.integral_floorQuadricMeasure_top` (New/Spanning/Frames/FiberMeasures.lean).

*Proof.* The vector $y = v_t(x)$ has $\langle z, y\rangle = t$, and it has norm $-N$ exactly when $x^*x = \alpha_t$. Write the top quadric in the flat chart of a hyperbolic basis. Then $(t, x) \mapsto v_t(x)$, with $x$ on the sphere of index $\delta\alpha_t$, is measure preserving onto the quadric up to the factor $|\pi|^{-1}$, which is $|N|^{-1/2}$ (`New.Floors.HyperbolicBasis.measurePreserving_vectorOfLastEntry_flatChart`). Fubini over $t$ concludes. $\square$

### The form of the top floor

**Definition (Scaled orbital integral).** For heads $p$ and $l \in \mathsf{G}$, let $w_p$ be the Weyl element of $p$ and

$$S_p(l) = \kappa_\varrho(p, 1)\,\mathcal{O}(W_Z)(w_pl^{-1}),$$

the head density times the orbital integral of $W_Z$ at $w_pl^{-1}$. The unfolded pairing is $u_l(y_1, y_2) = \langle W_Z(y_1), W_Z(y_2)\rangle\langle W_Z((w_ql^{-1})^{-1}y_2), W_Z((w_pl^{-1})^{-1}y_1)\rangle$.

Lean: `New.Floors.PlaceData.scaledOrbitalIntegral`, `New.Floors.PlaceData.unfoldedPairing` (New/Spanning/Frames/TopCorrelation.lean).

**Lemma.** For $l \in G^{(\varrho)}$, $\langle S_p(l), S_q(l)\rangle = \kappa_\varrho(p, q)\int u_l\,d(\mathsf{M}\times\mathsf{M})$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.inner_scaledOrbitalIntegral` (New/Spanning/Frames/TopCorrelation.lean).

*Proof.* The head densities multiply: $\kappa_\varrho(p, q) = \kappa_\varrho(p, 1)\kappa_\varrho(q, 1)$. A gauge for which $p$ and $q$ are heads (`New.Floors.IntegralPlace.IsLargeLatticeData.exists_gauge_isHead`) makes $u_l$ integrable, and Fubini writes the inner product of the two orbital integrals as the double integral. $\square$

**Theorem (The top form as an integral over links).** Let $\varphi(x) = \psi(\xi\,\langle z, xz\rangle)$. Then $f(l) = \varphi(l^{-1})\langle S_p(l), S_q(l)\rangle$ is integrable for the measure of the top floors, and its integral is $\mathcal{I}_\varrho(p, q, W_Z, \varphi)$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.floorForm_top_eq_integral` (New/Spanning/Frames/TopCorrelation.lean).

*Proof.* By the lemma, $f(l)$ is $\kappa_\varrho(p, q)$ times the integral of $u_l$. Changes of variables carry $(l, y_1, y_2) \mapsto \varphi(l^{-1})u_l(y_1, y_2)$ to the integrand of the floor form, with the same law (`New.Floors.IntegralPlace.IsLargeLatticeData.identDistrib_unfoldedPairing`); this integrand is integrable, and Fubini concludes. $\square$

**Definition (Fibre pairing).** For a vector $e$, if $e = l^{-1}z$ for some $l \in G^{(\varrho)}$, then $P_{p,q}(e) = \int_H\langle S_p(kl), S_q(kl)\rangle\,dk$, with $l$ chosen and $H$ the fixer of $z$; otherwise $P_{p,q}(e) = 0$.

Lean: `New.Floors.PlaceData.fiberPairing`, `New.Floors.PlaceData.fiberPairing_orbitPoint` (New/Spanning/Frames/TopFloor.lean).

**Remark (Formalization).** The element $l$ is `h.choose`. Two choices differ by an element of $H$ on the left, and the measure on $H$ is right invariant, so the value is the same for every $l$ (`fiberPairing_orbitPoint`). Off the orbit the value $0$ is a convention.

**Theorem (Positive type).** Let $R$ be a positive semidefinite matrix indexed by $j$ and $\omega_a$ heads. Then $\sum_{a,b}R_{ab}\langle S_{\omega_a}(l), S_{\omega_b}(l)\rangle \ge 0$, and $\sum_{a,b}R_{ab}P_{\omega_a,\omega_b}(e) \ge 0$ for every $e$.

Lean: `New.Floors.PlaceData.headSumNormSq_nonneg`, `New.Floors.IntegralPlace.IsLargeLatticeData.sum_fiberPairing_nonneg` (New/Spanning/Frames/TopFloor.lean).

*Proof.* Expand over the coordinates $c$: the sum is $\sum_cv_c^*Rv_c$ with $v_c(a) = S_{\omega_a}(l)_c$, and each term is $\ge 0$. The second sum is $0$ off the orbit, and on it the integral over $H$ of the first sum at $kl$. $\square$

**Theorem (The top form on the quadric).** For every continuous $\Phi$ equal to $P_{p,q}$ on the last vector quadric,

$$\mathcal{I}_\varrho(p, q, W_Z, \varphi) = \int\psi(\xi\langle z, e\rangle)\,\Phi(e)\,d\theta_{\mathrm{top}}(e).$$

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.floorForm_top_eq_integral_floorQuadric` (New/Spanning/Frames/TopFloor.lean).

*Proof.* The measure of the top floors is the measure of $H$ convolved with $\theta_\varrho$, and $l \mapsto l^{-1}z$ maps $\theta_\varrho$ to $\theta_{\mathrm{top}}$. Integrate first over $H$: this gives $P_{p,q}(l^{-1}z) = \Phi(l^{-1}z)$, and $\langle z, l^{-1}z\rangle$ is the last Gram entry. $\square$

### The density at the last entry

**Definition (Last entry density).** For $\pi\bar\pi = N$,

$$\rho_\pi(p, q) = |\pi|^{-1}\int P_{p,q}(v_{p_\varrho}(x))\,d\nu_{\delta\alpha_{p_\varrho}}(x).$$

Lean: `New.Floors.PlaceData.lastEntryDensity` (New/Spanning/Frames/TopFloor.lean).

The definition reads the last entry of $p$ only; it is used with $q_\varrho = p_\varrho$.

**Theorem (Fourier inversion at the last entry).** Let $F$ be a large lattice datum of the form `latticeMiddleGram 𝔰 N`, let the units of $A$ be open, $\pi\bar\pi = N$ and $\xi \in A$. Let $f(t) = \psi(\xi t)\,\rho_\pi(p^{(t)}, q^{(t)})$, where $p^{(t)}$, $q^{(t)}$ have last entry `unitOrOne t`. Then $f$ is integrable and $\int_Af(t)\,dt = \mathcal{I}_\varrho(p, q, W_Z, \varphi)$.

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.integral_lastEntryDensity` (New/Spanning/Frames/TopFloor.lean).

*Proof.* Extend $P_{p,q}$ to a continuous step function $\Phi$ of compact support (`New.Floors.IntegralPlace.IsLargeLatticeData.exists_step_function_eqOn_fiberPairing`). Apply the slicing theorem to $\psi(\xi\langle z, e\rangle)\Phi(e)$. Almost every $t$ is a unit. On the slice of such a $t$ the character is $\psi(\xi t)$, and the slice integral is $\rho_\pi(p^{(t)}, q^{(t)})$, since the fibre pairing does not read the entry $\varrho$ of the heads. The theorem on the top form on the quadric concludes. $\square$

**Remark (Formalization).** `unitOrOne t` is $t$ if $t$ is a unit and $1$ otherwise. The non-units are a null set, so the junk value $1$ does not change the integral.

**Theorem (Continuity and positivity).** The map $(p, q) \mapsto \rho_\pi(p, q)$ is continuous. If $R$ is positive semidefinite and all $\omega_a$ have the last entry $t$, then $\sum_{a,b}R_{ab}\rho_\pi(\omega_a, \omega_b)$ is a nonnegative real, and its real part, in $[0, \infty]$, is

$$|\pi|^{-1}\int^-\Bigl(\sum_{a,b}R_{ab}P_{\omega_a,\omega_b}(v_t(x))\Bigr)\,d\nu_{\delta\alpha_t}(x).$$

Lean: `New.Floors.IntegralPlace.IsLargeLatticeData.continuous_lastEntryDensity`, `New.Floors.IntegralPlace.IsLargeLatticeData.sum_lastEntryDensity_nonneg`, `New.Floors.IntegralPlace.IsLargeLatticeData.sum_lastEntryDensity_nonneg_and_eq_inv_mul_lintegral` (New/Spanning/Frames/TopFloor.lean).

*Proof.* Continuity: near $(p, q)$ the step function $\Phi$ does not change; only the sphere moves, and the fibre measures are weakly continuous in the index (`New.Floors.Place.IsDisintegration.continuous_integral`). Positivity: the sum of the densities is $|\pi|^{-1}$ times the integral of the fibre pairing sum (`New.Floors.PlaceData.sum_lastEntryDensity_eq`), which is $\ge 0$ pointwise by the theorem on positive type. For a nonnegative integrable function the lower integral of the real part equals the real part of the integral. $\square$
