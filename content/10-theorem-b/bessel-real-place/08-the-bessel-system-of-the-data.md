---
title: The Bessel system of the data
lean:
  - New/Spanning/Bessel/Basic.lean
  - New/Spanning/Bessel/FillingData.lean
decls:
  - New.Shape.scaledVolumeRatio
  - New.besselOrbitalIntegral
  - New.normalizedOrbitalIntegral
  - New.HasLocalBounds
  - New.BesselSystem
  - New.Data.unitarySignFrameY
  - New.Data.exists_unitary_schur_rep
  - New.Data.volU_div_volU_le
  - New.Data.scaledVolumeRatio_le
  - New.Data.weylDimensionPoly_mul_scaledVolumeRatio_le
  - New.IsBesselFunction.integral_dsKernel_mul_eq_of_convolve_eq
  - New.Data.isDiscreteSeriesBessel_filling_besselSystem
  - New.Data.levelX_zero_eq_comap
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Bessel system of the data

For admissible data $D$ and each infinite place $v$, this section gives one Bessel system and puts these systems into the filling data of [the plan of Theorem B](/chapter/theorem-b-plan/).

### Local bounds

The cut $W^\flat$ must have *local bounds*: forms on tuples of nonzero complex numbers that the sieve of [the chapter on the main term](/chapter/main-term/) takes as input. Two tensors enter them.

**Definition.** For a measure $\mu$ on a group, $W$ with values in $\mathbb{C}^I$ and $\gamma$ in the group, $J_W(\gamma) = \int W(y) \otimes \overline{W(\gamma^{-1}y)}\,d\mu(y)$. For $\sigma \in G_1$ and $p : \mathbb{N} \to \mathbb{C}^\times$, the *normalized orbital integral* is $J_W(w_p\sigma)$ for Lebesgue measure, times
$$\frac{\sqrt{c_G}\,(|p_\varrho|^2 - 1)^{(k-1)/2}}{|I|}\prod_{a < \varrho}|p_a|^{k+1+2(\varrho-a-1)},$$
where the Weyl element $w_p$ sends $e_a$ to $p_ae^*_a$ and $e^*_a$ to $e_a/\bar p_a$ for $a < \varrho$. Let $\Theta = \pi^{(2\varrho+1)k}\operatorname{vol}U(k)/\operatorname{vol}U(r)$.

Lean: `New.besselOrbitalIntegral`, `New.normalizedOrbitalIntegral`, `New.Shape.scaledVolumeRatio` (New/Spanning/Bessel/Basic.lean).

**Remark (Formalization).** The square root factor is $\sqrt{|p_\varrho|^2 - 1}^{\,k-1}$ with the real square root, which is $0$ for $|p_\varrho| < 1$. This is a junk value; part (b) below uses only $p_\varrho = h(z, \sigma z)$.

The structure of the local bounds is `New.SieveSystem` of New/Spanning/MainTerm/SieveSystem.lean, in [the chapter on the main term](/chapter/main-term/), a later chapter of this volume. Basic.lean imports it because local bounds are defined as a sieve system.

**Definition (from SieveSystem.lean).** Let $C$ be a commutative ring with a measure, $u : C \to U$, $\iota : U \to C$, $n \in \mathbb{N}$, forms $J_i$ on pairs of heads $p, q : \mathbb{N} \to U$, a function $\psi$ on $C$, a number $E_n$, weights $\Lambda_i$ and a decay $\beta$. They form a *sieve system* if: $\psi(0) = 1$; for $i \leq n$, with $p_i = q_i = u(c)$ put in, $\psi(\xi c)J_{i+1}$ is integrable in $c$, its integral is $J_i(p, q)$ for $\xi = 0$, and it has modulus at most $\beta(\xi)\Lambda_i(p)\Lambda_i(q)$ for a unit $\xi$; $J_{n+1}$ is continuous and positive semidefinite on heads with the same entry at position $n$; $|J_0| \leq E_n$; and for $i < n$, if $\xi = \iota(p_i) - \iota(q_i)$ is a unit, then $|J_{i+1}(p, q)| \leq \beta(\xi)\Lambda_{i+1}(p)\Lambda_{i+1}(q)$.

Lean: `New.SieveSystem` (New/Spanning/MainTerm/SieveSystem.lean).

**Definition (Local bounds).** Forms $J$ are *local bounds* for $W^\flat$ with degree $\deg$ and size $b$ if (a) they are a sieve system with $C = \mathbb{C}$, $\iota(z) = z^{-1}$, $n = \varrho$, the character $\psi(c) = e^{c - \bar c}$, $E_n = (1 + b^{-10})/\deg$, the head weights of exponent $n^6$ that vanish unless the partial products of the entries have modulus at most $b^{60n^2}$, and the decay $\beta(\xi) = \Theta\,b^{2000n^9}\,\ell_{k-n^7}(1/|\xi|)$ with $\ell_j(r) = r^j\min(1, r)^6$; and (b) for $\sigma$ in the floor group, which fixes the hyperbolic basis vectors, and heads $p, q$ with $p_\varrho = q_\varrho = Z(\sigma)_{\varrho\varrho}$, $J_n(p, q)$ is the inner product of the normalized orbital integrals of $W^\flat$ at $p$ and at $q$.

Lean: `New.HasLocalBounds` (New/Spanning/Bessel/Basic.lean).

### Bessel systems

**Definition (Bessel system).** A *Bessel system* with size $b$ and decay rate $f$ is a finite nonempty index set $I$, continuous $W, W^\flat : G_1 \to \mathbb{C}^I$, a degree $\deg > 0$ and a continuous unitary representation $\tau$ of $U(\kappa)$ on $\mathbb{C}^I$, such that: $(W, W^\flat)$ is a [cut pair](/chapter/bessel-real-place/#decay-and-the-cut) of type $\tau$; only scalars commute with $\tau$; for every $P \geq b^5$, $W$ has the [Schur bound](/chapter/bessel-real-place/#schur-bounds-and-orthonormality) $(P, |I|/\deg)$; $8r \leq b$; and $W^\flat$ has local bounds with forms that are part of the data.

Lean: `New.BesselSystem` (New/Spanning/Bessel/Basic.lean).

**Remark (Formalization).** The structure has no field for the continuity of $\tau$, and it does not ask $W$ to come from a discrete series. The type is a separate predicate, `New.Filling.IsDiscreteSeriesBessel` of [Section 3](/chapter/bessel-real-place/#bessel-functions-as-averages).

### The system at a real place

**Theorem.** For admissible data $D$ and each infinite place $v$ there is a Bessel system with size $D.b$, decay rate $D.f$ (the number of infinite places) and the shape of $Y_0$, whose type is the discrete series with doubled parameter $D.\mathrm{paramW}(v)$ and the weight with $D.\mathrm{columnCount}(v)$ columns.

Lean: [`New.Data.exists_besselSystem`](/decl/New.Data.exists_besselSystem/) (New/Spanning/Bessel/FillingData.lean).

*Proof.* (1) Choose an orthonormal frame with the signs of $Y_0$ (`New.Data.unitarySignFrameY`). Let $l$ be the parameter. Its gap is at least $r^7$ by the gap instance of the data, so $\deg_l > 0$, and by Harish-Chandra $\deg_l$ is the value of Weyl's dimension polynomial ([Volume 5](/chapter/discrete-series/)). (2) The Schur matrices of the weight, conjugated by a square root $B$ of their positive Gram matrix, give a continuous irreducible unitary $\tau$ with a unit vector $e$ whose coefficient is the coefficient of the lowest $K$-type. (3) The steep parameters of the data (`New.Data.exists_isSteep`) give a stationary point $x$ with $\ell(x) \leq b^{5n}$ and a large period ([Section 4](/chapter/bessel-real-place/#a-point-with-a-large-period)). (4) The normalized average $F$ at $x$ and its cut form a cut pair, and $F$ is fixed by $\deg_l c_l$ ([Section 5](/chapter/bessel-real-place/#decay-and-the-cut)). (5) The Schur bound follows from the fixed point property ([Section 6](/chapter/bessel-real-place/#schur-bounds-and-orthonormality)). (6) The local bounds come from the theorem below, with $\deg_l\Theta \leq b^{4r^2}$ and the size inequalities [`New.Data.realPlaceSizes`](/decl/New.Data.realPlaceSizes/). $\square$

**Lemma.** $\operatorname{vol}U(k)/\operatorname{vol}U(r) \leq (b^r)^r$, $\Theta \leq b^{2r^2}$, and the Weyl dimension times $\Theta$ is at most $b^{4r^2}$ if the entries of the parameter are at most $3a$.

Lean: `New.Data.volU_div_volU_le`, `New.Data.scaledVolumeRatio_le`, `New.Data.weylDimensionPoly_mul_scaledVolumeRatio_le` (New/Spanning/Bessel/FillingData.lean).

**Lemma.** If $F$ is a Bessel function fixed by convolution with $\deg_l c_l$, then each coordinate of $F$ is fixed by right convolution with the kernel of $l$ on $U(\varepsilon)$, carried over by the frame.

Lean: `New.IsBesselFunction.integral_dsKernel_mul_eq_of_convolve_eq` (New/Spanning/Bessel/FillingData.lean).

**Lemma.** The representation of step (2) exists: it is conjugate to the transposed Schur matrices of the transposes, irreducible, continuous, with the coefficient of a unit vector equal to the coefficient of the parameter.

Lean: `New.Data.exists_unitary_schur_rep`, `New.Data.unitarySignFrameY` (New/Spanning/Bessel/FillingData.lean).

Step (6) uses two results of [the chapter on real densities](/chapter/real-densities/), a later chapter, through the import of Frames/RealBandLimits.lean. The source proves the local bounds there because they need the floor measures of the real frames.

**Definition (from RealBandLimits.lean).** For $A, B : G_1 \to \mathbb{C}^I$ and $x \in G_1$, the matrix coefficient is $\langle A, R(x)B\rangle = \int_{\mathsf U\backslash G_1}\langle A(y), B(yx)\rangle\,dy$.

Lean: `New.Floors.quotientPairing` (New/Spanning/Frames/RealBandLimits.lean).

**Theorem (from RealBandLimits.lean).** Let $F$ be the cut of $W$ in the sense of `New.Floors.IsCutBessel` (a cut pair of irreducible type with the size inequalities). Let $\deg > 0$, $\int|\langle W, R(x)W\rangle|^2dx \leq |I|^2/\deg$, $\deg\,\Theta \leq b^{4r^2}$, $\deg\operatorname{vol}\{\|g\| \leq T\} \leq T^{9r^2}b^{99r^2}$ for $T \geq 1$, and $4000n \leq f$. Then $F$ has local bounds with degree $\deg$.

Lean: [`New.Floors.exists_hasLocalBounds_of_isCutBessel`](/decl/New.Floors.exists_hasLocalBounds_of_isCutBessel/) (New/Spanning/Frames/RealBandLimits.lean).

### The filling data

The structure `New.Filling` is defined in New/Spanning/Unfolding/Setup.lean, in [the chapter on the anatomy of a term](/chapter/anatomy-of-a-term/). The definition [`New.Data.filling`](/decl/New.Data.filling/) fills its fields from $D$ and takes the Bessel system at $v$ by choice from the theorem above.

**Lemma.** The Bessel system of `New.Data.filling` at $v$ has the type of the theorem. The level $K_X(0)$ of $D$ is the preimage of the principal level $K(M)$ under the embedding of $U(X_0)(\mathbb A_f)$.

Lean: `New.Data.isDiscreteSeriesBessel_filling_besselSystem`, `New.Data.levelX_zero_eq_comap` (New/Spanning/Bessel/FillingData.lean).

The second proof uses two lemmas of New/Spanning/Unfolding/Climbing.lean, in [the chapter on Poincaré series](/chapter/poincare-series/), a later chapter. They are proved there because the climbing argument needs the same description of the level. (i) For $k \in U(X_0)(\mathbb A_f)$, the image of $k$ lies in the lattice stabilizer if and only if $k$ is integral and its row at $k_0$ is congruent to that of $1$ modulo $\pi$. (ii) If the image lies there, then for each level prime $i$ and chosen place $w$, its reduction at $w$ is $1$ if and only if that of $k$ is $1$.

Lean: `New.Filling.inclHFin_mem_latticeStabilizer_iff`, `New.Filling.reduction_inclHFin_eq_one_iff` (New/Spanning/Unfolding/Climbing.lean).

**Remark (Formalization).** The filling data depend on choices: the frame `unitarySignFrameY` is `Nonempty.some`, and the Bessel system is `Exists.choose`. Later uses go only through the fields of the structure and the type predicate.
