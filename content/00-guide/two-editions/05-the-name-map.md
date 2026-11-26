---
title: The name map
lean:
  - Main.lean
  - New/Main.lean
  - New/Reduction/Data/FieldsAndPlaces.lean
  - New/Reduction/Data/AdmissibleData.lean
  - New/Reduction/PrimeSums.lean
  - New/Reduction/ShortAndEnough.lean
  - New/Reduction/MainInequality.lean
  - New/Reduction/OneSidedBound.lean
  - New/Reduction/Zeros/PrimeError.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The name map

This section maps the names of the compact edition to the names of the readable edition, for the declarations of the last part of the proof. Each name in the tables was found by a search in the tree of its edition at the pinned commit. Compact names are in the root namespace unless they start with `New.`. Readable names are in the namespace `New`. A name `Data.x` of the compact edition is the declaration `x` in the namespace `Data`; a name `New.Data.x` of the readable edition is the declaration `x` in the namespace `New.Data`. A field of a structure is marked "field".

The map is a map of roles, not of definitions. Two names in one row play the same part in the proof. Their definitions can differ in constants, in rounding and in the form of a hypothesis. The column "Note" says where they differ.

### The five theorems and the last step

These names are the same in both editions. They name different declarations in the two trees (Section 2).

| Compact | Readable | Note |
|---|---|---|
| `riemannHypothesis` | `riemannHypothesis` | same statement and proof term |
| `riemannZeta_eq_zero_re` | `riemannZeta_eq_zero_re` | same |
| `LFunction_ne_zero_of_half_lt_re` | `LFunction_ne_zero_of_half_lt_re` | same |
| `LFunction_eq_zero_re` | `LFunction_eq_zero_re` | same |
| `LFunction_eq_zero_re_of_isPrimitive` | `LFunction_eq_zero_re_of_isPrimitive` | same |
| `New.grh` | `New.grh` | compact in `New/Main.lean`, readable in `New/Reduction/OneSidedBound.lean` |
| `New.zeros_on_line` | `New.zeros_on_line` | compact proof by `grind` |
| `New.zeta_zeros_on_line` | `New.zeta_zeros_on_line` | compact proof by `grind` |

### The spine

| Compact | Readable | Note |
|---|---|---|
| `Data.short_forms` | `New.Data.span_short_integralRamified_eq_top`, `New.Data.indexLe_normalizedPoincare` | Theorem A; compact has parts (a) and (b) in one statement, with a rational scale $q$ |
| `Data.enough_forms` | `New.Data.enough_forms` | Theorem B; $\log(1+b^2)$ against $\log(1+2b^2)$ |
| `Data.integral_forms_long` | `New.Data.integral_forms_long` | Theorem C |
| `Data.exists_family_covolumeSq_le` | none | A and B together; readable does this in the proof of the main inequality |
| `star_inequality` | `New.star_inequality` | the same bound $f a \log^5 b$ |
| `primeError` | `New.primeRemainder` | the same definition |
| `lambdaClass` | `New.lambdaKResidueClass` | the weight $\lambda(n)$ |
| `lambdaSum` | `New.lambdaKSum` | the partial sums |
| `logDerivMean` | `New.logDerivMean` | the function $G_q$ |
| `entireL_ne_zero_of_primeError_le` | `New.LFunction_ne_zero_of_primeRemainder_le` | the criterion; compact conclusion on `entireL` |
| `eventually_primeError_le_rpow` | `New.eventually_primeRemainder_le_rpow` | $x^{8\varepsilon - 1/2}$ against $y^{-1/2+\varepsilon}$ |
| `IsPolar` | `New.IsPolar` | compact has the clause on $\operatorname{Re} s \geq 1$ |
| `IsPolar.exists_window_sub_mul_le` | none | the window lemma |
| `isPolar_primeError` | none | the transform of $R_M(e^v)$ |
| none | `New.eventually_abs_primeRemainder_le` | the prime number theorem for $R_q$ |
| none | `New.tendsto_primeRemainder` | $R_q(x) \to 0$ |
| none | `New.Data.primeRemainder_le` | the bound at $x$ in terms of $x_1$ |
| `exists_data` | `New.eventually_exists_data` | data at every large $x$ |

### The parameters

| Compact | Readable | Note |
|---|---|---|
| `Parameters` | `New.Parameters` | the structure |
| `N₀` (field) | `New.Parameters.q₀` (field) | the modulus, a multiple of $18480$ |
| `d` (field) | `New.Parameters.d` (field) | the prime |
| `dvd_N₀` (field) | `New.Parameters.dvd_q₀` (field) | $18480 \mid q_0$ |
| `d_congr` (field) | `New.Parameters.q₀_dvd_and_not_dvd` (field) | $q_0 \mid 2(d+1)$ and $q_0 \nmid d+1$ |
| `Parameters.c` | `New.Parameters.constantBound` | the constant that depends on $q_0$, $d$ only |
| `Parameters.N₁` | `New.Parameters.q₁` | the order of the root of unity of $E$ |
| `Parameters.Mω` | `New.Parameters.q₂` | the modulus of the congruences of the level primes |
| `Parameters.E` | `New.Parameters.E` | the field $E$ |
| `towerDeg` | `New.towerDeg` | the number of places $\equiv 1 \bmod q_0$ |

### The data and the sizes

| Compact | Readable | Note |
|---|---|---|
| `Data` | `New.Data` | the structure; compact stores $\log x, \log x_1, \log b$ only, readable also the integers $x, x_1, b$ |
| `s` (field) | `New.Data.towerExp` (field) | the exponent with $2^s = m^{22}$ |
| `m`, `r` (fields) | `New.Data.m`, `New.Data.r` (fields) | $m \in [\sqrt x, 2\sqrt x]$, $r \in [x^5, 3x^5]$ |
| `Data.tops` | `New.Data.aPlaces` | the places $\equiv 1 \bmod q_0$ |
| `thick` (field) | `New.Data.bPlaces` (field) | the places of weight $b$ |
| `Data.nominalWeight` | `New.Data.weight` (field) | weight $a/x$ or $a/x_1$; compact is the real quotient, and its integer weights `Data.b₁`, `Data.b₂` round up to multiples of $N_1$ |
| `g` (field) | `New.Data.levelPrime` (field) | the two primes $p_0, p_1 \in [b^{10}, b^{11}]$ |
| `Data.gProd` | `New.Data.M` | $M = p_0 p_1$ |
| `Data.N` | `New.Data.N` (field) | the level, a prime; compact chooses it by `choose` from the field `exists_prime_window`, readable has it as a field |
| `Data.a` | `New.Data.a` | compact: least multiple of $N_1$ at least $x b$; readable: $x b$ |
| `Data.budget` | `New.Data.errorUnit` | $f a \log^3 b$ |
| `Data.h₂` | `New.Data.halfGap` | half the gap |
| `Data.h` | `New.Data.gap` | the gap |
| `Data.rowDim` | `New.Data.targetDim` | the dimension of the target |
| `Data.dirCost` | `New.Data.directionAmount` | the amount per direction |
| `Data.mainHeight` | `New.Data.mainAmount` | $m k$ times the amount per direction |
| `Data.mainAsk` | `New.Data.mainPrimeSum` | the main part of a prime sum |
| `Data.remainder` | `New.Data.totalRemainder` | $\sum_\tau (s_{\mathrm{fin}}(a, \tau) - s_{\mathrm{main}})$ over the $a$-places |
| `Data.remainder_eq` | `New.Data.totalRemainder_eq` | the remainder through the $R_q$ |
| `Data.HasLogBound` | `New.Data.HasLogBound` | comparison of monomials on the scales |

### The objects of Theorems A, B and C

| Compact | Readable | Note |
|---|---|---|
| `Data.Column` | `New.Data.SourceForm` | the source forms, on a definite unitary group |
| `Data.ramifiedColumns` | `New.Data.ramifiedSourceForms` | the ramified source forms |
| `Data.rows` | `New.Data.targetForms` | the target forms, on an indefinite unitary group |
| `Data.G` | `New.Data.chosenGL` | the finite group of translates |
| `Data.projectedPoincare` | `New.Data.normalizedPoincare` | the maps $s\mathfrak p$; compact scaled by $q$ in Theorem A |
| `Data.integralRamified` | `New.Data.integralRamified` | the integral source forms |
| `Data.IndexLe` | `New.TwistedLattice.IndexLe` | the logarithmic index |
| `Data.IsFitFamily` | `New.Data.HasSmallRatios` | the families of twists of Theorem C |

### Settings

The readable settings file is `Lib/Speed.lean`. The compact one is `Lib/General/LinearAlgebra/Base.lean`, which also restates about twenty matrix lemmas of Mathlib with classical decidability (F-116). The synonym of `IsEmpty` is `New.IsVoid` in the readable edition and `IsVoid` in the root namespace in the compact edition. A proof copied from one edition to the other can fail because the simp set and the instance priorities differ.

### Letters

The compact `GUIDE.md` (24 lines) is a table of letters. The readable `GUIDE.md` (155 lines) has a glossary. The letters that differ most are these: $N_0, N_1$ for $q_0, q_1$; "tops" and "thick places" for $a$-places and $b$-places; $g_0, g_1$ and $g$ for $p_0, p_1$ and $M$; $h_{\mathrm{main}}$ and $\mathcal{U}$ for the main amount and the amount per direction; $\mathcal B$ for the error unit. The compact spine comment calls the source forms "columns" and the target forms "rows".

**Remark.** The map does not go below Theorems A, B and C. The compact folders `Columns`, `Rows`, `Seesaw`, `Selmer`, `Heights` and others do not match the readable folders `UpperBound`, `Spanning`, `Determinant`, `OneLift` and `Congruences` one to one. A reader who follows a lemma of the readable edition into the compact one should search by statement, not by name.
