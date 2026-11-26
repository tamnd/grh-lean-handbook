---
title: Junk values and constants that may vanish
lean:
  - New/Reduction/Zeros/PrimeError.lean
  - Lib/Analytic/EntireLFunction.lean
  - New/Determinant/Twist/FitTwists.lean
  - New/OneLift/HeckeValues/TwistedRatio.lean
  - New/Spanning/Unfolding/Setup.lean
  - New/Spanning/Unfolding/AmplitudeSums.lean
  - New/UpperBound/Seesaw/SeesawIdentity.lean
  - New/Main.lean
decls:
  - New.isPolar_primeRemainder
  - New.IsPolar
  - New.Data.CriticalPair.ratio
  - New.Data.CriticalPair.ratio_eq_algPart_div
  - New.Filling.amplitude
  - New.Filling.amplitudeSum
  - New.Filling.summable_amplitude
  - New.Data.RankOneIndex
  - New.Data.seesaw_identity
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Junk values and constants that may vanish

In Lean every function is total. A function of type `ℝ → ℝ` has a value at every real number. So Lean must give a value to $1/0$, to $\log 0$, to the sum of a divergent series and to the integral of a function that is not integrable. Mathlib chooses a value, almost always $0$, and proves lemmas about it. A mathematician calls such a value undefined. This book calls it a junk value. The convention makes many statements shorter, because a lemma needs no hypothesis to make its terms meaningful. It also has a cost for the reader. A statement with a junk value can be true for a reason that is not the classical reason, and it can say less than its text seems to say. This section lists the conventions that occur in the source, and shows on real declarations where they matter. It ends with the related problem of constants that the source does not show to be nonzero.

### The conventions

These are the junk values of Mathlib that a reader of this source meets.

1. Division and inverse: $x/0 = 0$ and $0^{-1} = 0$ in every field (`div_zero` (Mathlib), `inv_zero` (Mathlib)).
2. Logarithm: $\log 0 = 0$ and $\log x = \log |x|$ for $x < 0$ (`Real.log_zero` (Mathlib), `Real.log_neg_eq_log` (Mathlib)).
3. Subtraction in `ℕ`: $a - b = 0$ if $a \leq b$ (`Nat.sub_eq_zero_of_le` (Mathlib)). The floor `⌊y⌋₊` of a negative real is $0$ (`Nat.floor_of_nonpos` (Mathlib)).
4. Powers: in `ℂ`, $0^{s} = 0$ for $s \neq 0$, so the term $l = 0$ of a series $\sum_l l^{-s}$ is $0$. A real power $x^y$ with $x < 0$ has a value with no classical meaning.
5. Series: the sum `∑' n, f n` is the sum of the family if it is summable, and $0$ otherwise (`tsum_eq_zero_of_not_summable` (Mathlib)). Summable means unconditionally summable: the finite partial sums over all finite sets converge along the filter of finite sets. In $\mathbb{R}$, $\mathbb{C}$ and every finite-dimensional normed space this is absolute convergence. So a series that converges only conditionally, as $\sum (-1)^n/n$, has the Lean sum $0$.
6. Integrals: the Bochner integral `∫ x, f x ∂μ` is the integral if $f$ is integrable, and $0$ otherwise (`MeasureTheory.integral_undef` (Mathlib)). Integrable means measurable in a suitable sense and absolutely integrable. So an improper integral that converges only conditionally, as $\int_0^\infty \sin x / x\,dx$, also has the Lean value $0$.
7. Poles: functions with poles get values there. The function $\Gamma$ of Mathlib is $0$ at its poles, so the gamma factor $\Gamma_{\mathbb{R}}(s) = \pi^{-s/2}\Gamma(s/2)$ is $0$ at $s = 0, -2, -4, \dots$. A comment in `New/Main.lean` says: "the gamma factor has no pole in `0 < re s` (Mathlib gives it the value `0` at a pole)". An L-function at its pole has a finite value, as Section 1 says.

The integral of a function with values in $[0, \infty]$ is different. The Lebesgue integral `∫⁻ x, f x ∂μ` of such a function always has its classical value in $[0, \infty]$, and the value $\infty$ is a real value, not a junk value. The same holds for a sum `∑'` of a family with values in $[0, \infty]$, which always converges there. The map `ENNReal.toReal` from $[0, \infty]$ to $\mathbb{R}$ sends $\infty$ to $0$, and this is a junk value again.

The conventions give one rule that a reader uses often.

**Lemma.** Let $f$ be a family with values in a normed space. If $\sum' f \neq 0$, then $f$ is summable. If $\int f\,d\mu \neq 0$, then $f$ is integrable.

Mathlib: `tsum_eq_zero_of_not_summable` (Mathlib), `MeasureTheory.integral_undef` (Mathlib).

*Proof.* These are the contrapositives of the two conventions. $\square$

So a statement that a series or an integral is nonzero, or has a nonzero lower bound, implies convergence. A statement that a series or an integral equals a given number does not, if the number can be $0$. An upper bound $|\sum' f| \leq B$ with $B \geq 0$ says nothing about convergence.

### A division by zero that has the right value

The first example is in the analytic part of the argument. The criterion of Landau type in [the Landau criterion](/chapter/landau-criterion/) uses a predicate on a pair of functions.

**Definition (Polar).** Let $E : \mathbb{R} \to \mathbb{R}$ and $r : \mathbb{C} \to \mathbb{C}$. The pair $(E, r)$ is polar if $E$ is measurable and there are $C \in \mathbb{R}$ and a meromorphic function $\Phi$ on $\mathbb{C}$ with these three properties: (a) $|E(v)| \leq C e^v$ for $v \geq 0$; (b) $\Phi(s) = \int_0^\infty E(v) e^{(1-s)v}\,dv$ for $\operatorname{Re} s > 2$; (c) for every $\rho$ with $\operatorname{Re} \rho > 0$, $(z - \rho)\Phi(z) \to r(\rho)$ as $z \to \rho$, $z \neq \rho$.

Lean: `New.IsPolar` (Lib/Analytic/EntireLFunction.lean).

The Lean text is this.

```lean
def IsPolar (E : ℝ → ℝ) (r : ℂ → ℂ) : Prop :=
  Measurable E ∧
  ∃ (C : ℝ) (Φ : ℂ → ℂ),
    Meromorphic Φ ∧
    -- (a) exponential growth
    (∀ v ≥ (0 : ℝ), |E v| ≤ C * Real.exp v) ∧
    -- (b) `Φ` is the transform of `E` far to the right
    (∀ s : ℂ, 2 < re s → Φ s = ∫ v : ℝ in Ioi 0, E v * Complex.exp ((1 - s) * v)) ∧
    -- (c) at most simple poles in `re ρ > 0`, with residues `r ρ`
    ∀ ρ : ℂ, 0 < re ρ → Tendsto (fun z ↦ (z - ρ) * Φ z) (𝓝[≠] ρ) (𝓝 (r ρ))
```

**Remark (Formalization).** Clause (b) uses a Bochner integral, so read alone it would hold with the value $0$ for a function $E$ that is not integrable against $e^{(1-s)v}$. Clause (a) prevents this. With (a) and the measurability of $E$, the lemma `New.integrableOn_laplace_of_abs_le` of the same file proves that the integrand is integrable on $(0, \infty)$ for $\operatorname{Re} s > 2$. So (b) is the classical statement. Clause (c) is a statement about a limit (Section 5). It says that $\Phi$ has at most a simple pole at $\rho$, with residue $r(\rho)$, and $r(\rho) = 0$ means that $\Phi$ has no pole there. The value $\Phi(\rho)$ itself plays no part.

**Proposition.** Let $d \equiv 7 \pmod 8$ be a prime, and let $q \geq 1$ be prime to $d$. Then the pair formed by $v \mapsto R_q(e^v)$ and
$$r(s) = \frac{1}{\varphi(q)\, s(1 - s)} \sum_{\psi \bmod q} \bigl(\operatorname{ord}_s E_\psi - \operatorname{ord}_s E_{\psi\chi_K}\bigr)$$
is polar. Here $E_\psi$ is the entire function `entireL ψ`, equal to $L(s, \psi)$, times $s - 1$ if $\psi$ is principal, and $\operatorname{ord}_s$ is the order of the zero at $s$.

Lean: `New.isPolar_primeRemainder` (New/Reduction/Zeros/PrimeError.lean).

```lean
lemma isPolar_primeRemainder (hd : d % 8 = 7) (h_cop : q.Coprime d) :
    IsPolar (fun v : ℝ ↦ primeRemainder d q (Real.exp v)) fun s : ℂ ↦
      (∑ ψ : DirichletCharacter ℂ q,
        (analyticOrderNatAt (entireL ψ) s - analyticOrderNatAt (entireL (quadTwist ψ d)) s : ℂ)) /
        φ q / (s * (1 - s)) := by
```

The proof is in [the weighted prime remainder](/chapter/weighted-prime-remainder/), where this is [Proposition](/decl/New.isPolar_primeRemainder/).

**Remark (Formalization).** At $s = 1$ the formula for $r$ is a division by $s(1 - s) = 0$. In Lean its value is $0$. The docstring of the source says so: the continuation "has no pole at `1`, where the formula below is a division by zero, of value `0`." The function $\Phi$ of the proof is $F(s)/(s - 1)$ with $F(1) = 0$, so it has no pole at $1$, and its residue there is $0$. So the statement is true at $s = 1$, but only because the junk value of the formula is the right number. A reader who reads the formula classically would say that the residue at $1$ is undefined, or infinite. The orders are natural numbers (`analyticOrderNatAt` (Mathlib)), cast to `ℂ` before the subtraction, so the difference is a true integer difference and not a truncated one.

### A ratio with a denominator that may vanish

The second example is in the lower bound of Theorem C.

**Definition.** For a critical pair $p = (\nu, z)$ of the data, a tame character $\vartheta$ and a sign $s \in \{\pm 1\}$, the ratio of $p$ at $\vartheta$ is the complex number
$$\frac{|L^{S \cup Q}(z, (\nu\vartheta^{s})^{-1})|}{|L^{S}(z, \nu^{-1})|},$$
where $S$ is the set of chosen places, $Q$ is the set of places of $\vartheta$, and $L^{T}$ omits the Euler factors at $T$ and at the conjugates. The default sign is $s = 1$.

Lean: `New.Data.CriticalPair.ratio` (New/Determinant/Twist/FitTwists.lean).

```lean
noncomputable def CriticalPair.ratio (p : D.CriticalPair) (ϑ : D.TameChar) (s : ℤˣ := 1) : ℂ :=
  (‖(p.character * ϑ.toAutChar ^ (s : ℤ))⁻¹.L ({w : FinPlace D.E | D.IsChosen w} ∪ ϑ.Q) p.z‖ /
    ‖p.character⁻¹.L {w : FinPlace D.E | D.IsChosen w} p.z‖ : ℂ)
```

The sign $s$ has type `ℤˣ`, the units $\{\pm 1\}$ of $\mathbb{Z}$, and `(s : ℤ) := 1` is a default argument: a user who omits it gets $s = 1$. The quotient is a quotient of real norms, cast to `ℂ` by the ascription `: ℂ`.

**Remark (Formalization).** If the denominator is $0$, the ratio is $0$ by the convention $x/0 = 0$. So the definition alone does not make the ratio positive, and a lemma that uses its positivity must get it from elsewhere. The source gets it from the algebraic part. [Theorem](/decl/New.Data.CriticalPair.ratio_eq_algPart_div/) below writes the ratio as a quotient of two algebraic parts, and `New.Data.CriticalPair.algPart_pos` proves that each algebraic part is positive. The L-values are also nonzero by `New.Data.CriticalPair.L_mul_ne_zero`. This is finding F-033 of the register.

**Theorem.** Let $p = (\nu, z)$ be a critical pair, let $n$ be a finite index set with $2z$ elements and $z \geq 2$, and let $\vartheta$ be a tame character. Then the ratio of $p$ at $\vartheta$, with the default sign, is the quotient of the algebraic part of $\nu\vartheta$ by the algebraic part of $\nu$.

Lean: `New.Data.CriticalPair.ratio_eq_algPart_div` (New/OneLift/HeckeValues/TwistedRatio.lean).

```lean
theorem ratio_eq_algPart_div (H : p.HasLiftRank n) (ϑ : D.TameChar) :
    p.ratio ϑ = algPart H ϑ / algPart H TameChar.one := by
```

The positivity is stated in `ℂ` with the scoped order `ComplexOrder`: the line `open scoped ComplexOrder in` comes before `lemma algPart_pos (H : p.HasLiftRank n) (ϑ : D.TameChar) : 0 < algPart H ϑ := by`. In this order, $0 < w$ for $w \in \mathbb{C}$ means that $w$ is real and positive. A reader who sees `0 < w` with `w : ℂ` must look for this line.

### Sums and integrals that may diverge

The third example is in the spanning theorem, which gives Theorem B of [the three theorems](/chapter/theorems-a-b-c/). Its amplitudes are integrals over the archimedean group, and its amplitude sums are series over sets of rational points.

**Definition.** For classes $c, c'$ and a rational point $\gamma$, the amplitude is the Bochner integral
$$A(c, c', \gamma) = \int \beta_c(y)\,\beta_{c'}(\gamma^{-1} y)\, W(y) \otimes W(\gamma^{-1} y)^*\,dy,$$
with values in a finite-dimensional complex space. For a set $T$ of rational points, the amplitude sum $A_T(c, s, c')$ is the sum $\sum'$ of $A(c, c', \gamma)$ over the $\gamma \in T$ that are terms over $(c, s, c')$.

Lean: `New.Filling.amplitude`, `New.Filling.amplitudeSum` (New/Spanning/Unfolding/Setup.lean).

```lean
def amplitude (c c' : S.Classes) (γ : S.G E) : EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord) :=
  ∫ y : InfinitePlace E → 𝔰.G₁,
    (S.classCutoff c y * S.classCutoff c' ((S.ratToInf γ)⁻¹ * y)).toReal • S.besselKernel side γ y
```

```lean
def amplitudeSum (T : Set (S.G E)) (c : S.Classes) (s : S.ResidueGL) (c' : S.Classes) :
    EuclideanSpace ℂ (S.BesselCoord × S.BesselCoord) :=
  ∑' γ : ↥(T ∩ S.termsOver c s c'), S.amplitude side c c' γ
```

**Remark (Formalization).** Both definitions have junk values. The amplitude is $0$ if its integrand is not integrable. The amplitude sum is $0$ if the family is not summable. The cutoffs have values in $[0, \infty]$, and `.toReal` sends $\infty$ to $0$. An identity that exchanges the sum and the integral, as the unfolding of a Poincaré series does, needs summability and integrability as explicit inputs, or both of its sides can be $0$ for a junk reason (finding F-032). The source proves the inputs with a majorant: the integral `New.Filling.amplitudeMajorant`, with values in $[0, \infty]$, has no junk value, and `New.Filling.tsum_amplitudeMajorant_lt_top` (New/Spanning/Unfolding/AmplitudeSums.lean) proves that the sum of the majorants is finite. Then the next lemma follows.

**Lemma.** For an admissible filling, every set $T$ and all $c, s, c'$, the family of the amplitudes $A(c, c', \gamma)$, $\gamma \in T$ a term over $(c, s, c')$, is summable.

Lean: `New.Filling.summable_amplitude` (New/Spanning/Unfolding/AmplitudeSums.lean).

*Proof.* The norm of each amplitude is at most its majorant. The sum of the majorants over all classes $c'$ is finite by `New.Filling.tsum_amplitudeMajorant_lt_top`. A family whose norms have a finite sum is summable. $\square$

### Truncated subtraction

The fourth example hides a bound in a type.

**Definition.** For $z \in \mathbb{N}$, the index type `RankOneIndex z` is the disjoint union of four finite sets with $12$, $4$, $4$ and $2z - 20$ elements, where $2z - 20$ is the truncated difference in $\mathbb{N}$.

Lean: `New.Data.RankOneIndex` (New/Determinant/Twist/FitTwists.lean).

```lean
abbrev RankOneIndex (z : ℕ) : Type := (Fin 12 ⊕ Fin 4 ⊕ Fin 4) ⊕ Fin (2 * z - 20)
```

**Remark (Formalization).** The type has $20 + (2z - 20)$ elements. This is $2z$ if $z \geq 10$, and $20$ if $z < 10$. The field `hasLiftRank` of a main pair asks that the type has $2z$ elements. So this field forces $z \geq 10$, although its docstring says only "`2 ≤ z`" (findings F-038 and F-111). For the main pairs nothing is lost, since $z > m$ and $m$ is large. The same rule applies to the field `sparse` of the admissible data in `New/Reduction/Data/Existence.lean`, which has the bound `(r + 1 - m) * (5 * r)`: the difference $r + 1 - m$ is a truncated difference, and it is the classical difference because $m \leq r$.

### Constants that may be zero

A related problem is not a junk value. Some theorems of the source give a constant $c$ with an identity $X = cY$, and the theorem does not say that $c$ is nonzero, or it says that $c$ is nonzero but the identity can still hold because both sides are $0$. A reader who assumes more than the statement says can read too much into it. Risk R6 of the plan of this book names this problem, and the class `vanishing` of the register of findings lists each case (findings F-068 to F-075).

**Theorem (Seesaw identity).** Let $t$ be a linear form on the values of forms on $X_0$, and let $g$ be an archimedean point of $U(Y_0)$. Then there is a unit $c \in \mathbb{C}^\times$ such that every twist $\vartheta$ has a chain datum $\Psi$ with $\mathrm{lowerChain}_\vartheta(\mathcal{P}\varphi) = c \cdot \mathrm{compositeLift}_\vartheta(\Psi)(\varphi)$ for every ramified source form $\varphi$, where $\mathcal{P}$ is the Poincaré map at $g$ and $t$.

Lean: `New.Data.seesaw_identity` (New/UpperBound/Seesaw/SeesawIdentity.lean).

```lean
theorem seesaw_identity {P : Parameters} {D : Data P}
    (t : (WeylIndex (D.X 0) D.columnCount → ℂ) →ₗ[ℂ] ℂ) (g : GInf D.E (D.signsY 0)) :
    ∃ c : ℂˣ, ∀ ϑ : D.Twist, ∃ Ψ : D.Translations →₀ ℂ, IsChainDatum ϑ Ψ ∧
      ∀ φ : D.ramifiedSourceForms,
        lowerChain ϑ (D.poincareAt g t φ) = (c : ℂ) • compositeLift ϑ Ψ φ := by
```

**Remark (Formalization).** The constant is a unit, `c : ℂˣ`, so $c \neq 0$. But the identity can be trivial. The proof sets `let u : ℂˣ := normUnit (c₀ * C / (D.residueMatrixCount ^ (2 * D.m) : ℕ))`, and its comment says: "If this number is `0`, then `u = 1` and `u • c₀ • seesawDatum ϑ = 0`." In that case both sides of the identity are $0$. So the theorem alone does not show that the lower chain of a Poincaré series is nonzero. That must come from another part of the argument (finding F-068, which the register marks as open, and F-110 on the docstring of `New.Data.seesawConst`, which calls the chosen constant "a non-zero constant"). The other cases of the class `vanishing` have the same form: a factor $\kappa$ in the one square identity that is not shown nonzero (F-069), a constant $C$ of the exchange identity with only its sign used (F-070), a constant $C$ in a norm bound that may be $0$ (F-071), and the branching matrix and the factor $\beta$ of a definite theta lift, not shown nonzero at their definition (F-073, F-074). For each, a chapter of this book that states the result says where the nonvanishing comes back, or that the register has the question open.

### What to take from this section

Risk R5 of the plan of this book is that junk values and chosen objects hide the content of a statement. The rule for a reader is short. For each division, find the place where the denominator is shown nonzero. For each `∑'` and each `∫`, find the summability or the integrability. For each `-` between natural numbers, find the inequality that makes it a true difference. For each constant in an identity, ask whether the identity can be $0 = 0$. In this book each such place has a `**Remark (Formalization).**`.
