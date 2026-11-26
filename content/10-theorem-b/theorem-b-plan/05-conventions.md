---
title: Conventions that change the meaning
lean:
  - New/Spanning/Unfolding/Setup.lean
  - New/Spanning/Unfolding/AmplitudeSums.lean
  - New/Spanning/Unfolding/CutoffIntegral.lean
  - New/Spanning/Unfolding/FillingAdmissible.lean
  - New/Spanning/Frames/RealPlaceGauge.lean
  - New/Spanning/Bessel/FillingData.lean
decls:
  - New.Filling
  - New.Filling.IsAdmissible
  - New.Filling.ten_pow_five_le_varrho
  - New.Floors.RealPlaceSizes
  - New.Floors.RealPlaceSizes.ten_pow_le_varrho
  - New.Data.realPlaceSizes
  - New.Filling.amplitude
  - New.Filling.amplitudeSum
  - New.Filling.summable_amplitude
  - New.Filling.tsum_amplitudeMajorant_lt_top
  - New.Filling.classCutoff
  - New.Filling.exists_classCutoff_eq_mul
  - New.Filling.lintegral_classCutoff_eq_unipotentCovolume
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Conventions that change the meaning

The statements of the earlier sections use definitions that take a value even where the classical object does not exist. This section lists these conventions. The sizes of the data are in [the data and its sizes](/chapter/data-and-sizes/).

### Filling data and the standing hypotheses

The theorems of layers 3 and 4 are stated for *filling data* $S$, a structure that collects a CM field $E$, a shape, the two level primes $p_0, p_1$, the chosen places above them, a generator of the different, the base $b$ and the cutoffs. Its fields include size conditions, for example $b \geq 1000$, $k \leq b$, $\varrho + 1 \leq b$ and $10^5 \leq \varrho$, where $\varrho$ is the number of hyperbolic planes and $k$ the rank of $X_0$.

Lean: `New.Filling`, `New.Filling.ten_pow_five_le_varrho` (New/Spanning/Unfolding/Setup.lean).

The bounds of layer 4 also take the standing hypotheses `IsAdmissible`. They say that the level of the source is the preimage of the principal congruence subgroup $K(M)$, that reduction at the chosen places maps the stabilizer of the lattice onto $\bar G$, and that a list of size inequalities holds. Two of these inequalities fix the ratio of the two second moments:

$$b^{11kf}\,\mathcal{D}_{\mathrm{id}} \leq \mathcal{D}_{\mathrm{main}} \leq (M/b^6)^{kf}\,\mathcal{D}_{\mathrm{id}}.$$

Lean: `New.Filling.IsAdmissible` (New/Spanning/Unfolding/Setup.lean).

For the filling of the admissible data $D$, these hypotheses are not assumed. The source proves them as an instance, in [FillingAdmissible.lean](lean:New/Spanning/Unfolding/FillingAdmissible.lean#L743). Lean accepts this instance, if the reported checks hold. So every theorem of layer 4, applied to $D$, has no open hypothesis of this kind.

**Remark (Formalization).** One field of `IsAdmissible` bounds a relative index of subgroups from below by $(N^k/b)^f$. In Lean the relative index is $0$ when it is infinite. Since $(N^k/b)^f > 0$, the field also says that the index is finite.

### Two thresholds for the number of planes

Two lower bounds for $\varrho$ appear in the source. The filling data ask $10^5 \leq \varrho$. This is the bound that the unfolding, the remaining terms and the main term use. The local bounds for cut Bessel functions at a real place use a separate structure of sizes.

**Definition (Sizes at a real place).** For a shape, a box radius $\rho$, an exponent $s$ and a base $b$, the *sizes at a real place* hold if $\rho = b^{6n + 2}$, $8r \leq \rho$, $k = s + 3n + 6$, $10^9 n^3 < s$, $n^7 \leq k$, $10^8 \leq \varrho$ and $2 \leq b$. Here $n = \varrho + 1$ and $r$ is the rank of the whole space.

Lean: `New.Floors.RealPlaceSizes`, `New.Floors.RealPlaceSizes.ten_pow_le_varrho` (New/Spanning/Frames/RealPlaceGauge.lean). The structure starts at [line 290](lean:New/Spanning/Frames/RealPlaceGauge.lean#L290) and the field for $10^8$ is at [line 302](lean:New/Spanning/Frames/RealPlaceGauge.lean#L302).

**Lemma (The data have the sizes at a real place).** The sizes at a real place hold for the shape of $Y_0$ of $D$, with box radius $b^{6n + 2}$, exponent $k - (3n + 6)$ and base $b$.

Lean: `New.Data.realPlaceSizes` (New/Spanning/Bessel/FillingData.lean).

The proof of [the Bessel systems](/decl/New.Data.exists_besselSystem/) uses this lemma. Both thresholds come from the logarithmic size bounds of $D$, and $10^8$ implies $10^5$. So the two do not conflict.

**Remark (Formalization).** A reader who reads only the structure of filling data sees $10^5$. The threshold that the data $D$ must meet is $10^8$, and it enters only through the Bessel systems at the real places.

### Values where an integral or a sum does not converge

The amplitude of a term $\gamma$ over the classes $c, c'$ is the Bochner integral

$$\int \beta_c(y)\,\beta_{c'}(\gamma^{-1}y)\, W(y)\otimes\overline{W(\gamma^{-1}y)}\, dy.$$

The amplitude sum over a set $T$ of terms is the sum of the amplitudes of the elements of $T$ over the block $(c, s, c')$.

Lean: `New.Filling.amplitude`, `New.Filling.amplitudeSum` (New/Spanning/Unfolding/Setup.lean).

**Remark (Formalization).** In Lean a Bochner integral of a function that is not integrable is $0$, and a sum `tsum` of a family that is not summable is $0$. The cutoffs take values in $[0, \infty]$, and the passage to real numbers sends $\infty$ to $0$. So an upper bound for an amplitude sum means what it says only if the family converges. The source proves convergence in two theorems.

**Theorem (Summability of the amplitudes).** Let $S$ be admissible. For every set $T$ of terms, every class $c$ and every reduction $s$, the sum over all classes $d$ and all terms $\gamma \in T$ over $(c, s, d)$ of the integrals

$$\int \beta_c(y)\,\beta_d(\gamma^{-1}y)\,\bigl\|W(y)\otimes\overline{W(\gamma^{-1}y)}\bigr\|\, dy$$

is finite. Hence for each class $c'$ the amplitudes of the elements of $T$ over $(c, s, c')$ are summable.

Lean: `New.Filling.tsum_amplitudeMajorant_lt_top`, `New.Filling.summable_amplitude` (New/Spanning/Unfolding/AmplitudeSums.lean).

The final statement of Theorem B is about dimensions and has no such convention. The chain to it starts from the Petersson formula, whose left side is an inner product of forms, so a value $0$ cannot make it empty. [The chapter on moments](/chapter/moments/) shows each exchange of a sum and an integral with its convergence.

### The cutoff is a choice

The cutoff $\beta_c$ of a class $c$ is not given by a formula. The source proves that a cutoff exists for the group of rational unipotent points of the class, takes one by choice, and multiplies it by the indicator of the reduced points. The definition is marked irreducible. So later proofs can use only the stated properties.

**Lemma (Properties of the cutoff).** For each class $c$ there is a measurable function $\beta$ such that $\beta_c = \beta\cdot\mathbf{1}_{\mathrm{red}}$, where $\mathbf{1}_{\mathrm{red}}$ is the indicator of the reduced points, and $\sum_u \beta(u y) = 1$ for all $y$, the sum over the rational unipotent points $u$ of the class at level $M$.

Lean: `New.Filling.classCutoff`, `New.Filling.exists_classCutoff_eq_mul` (New/Spanning/Unfolding/Setup.lean).

If $E$ contains a primitive $5040$-th root of unity, the integral of $\beta_c$ over the real unipotent group is the explicit number $\nu$, the same for every class.

Lean: `New.Filling.lintegral_classCutoff_eq_unipotentCovolume` (New/Spanning/Unfolding/CutoffIntegral.lean).

**Remark (Formalization).** The amplitudes, the scaled Poincaré map and the maps $s\mathfrak{p}$ of Theorem B depend on the choice of the cutoffs and of the Bessel system at each real place, taken from [the theorem on Bessel systems](/decl/New.Data.exists_besselSystem/). So Theorem B is a statement about these chosen maps. Its proof uses only the stated properties of the choices.
