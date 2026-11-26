---
title: Existence, choice and data
lean:
  - Lib/Analytic/ZeroSymmetry.lean
  - New/Reduction/ShortAndEnough.lean
  - New/UpperBound/Divisibility/LocalDivisibility.lean
  - Lib/Adelic/QuotientMeasure/Basic.lean
  - New/Spanning/Unfolding/Setup.lean
  - New/Reduction/Data/FieldsAndPlaces.lean
  - New/Reduction/Data/AdmissibleData.lean
decls:
  - New.exists_isPrimitive_changeLevel_eq
  - New.Data.exists_err_gaugeLe_compositeLift
  - New.Data.divisibilityError
  - New.Data.seesawConst
  - New.chosenCutoff
  - New.Filling.classCutoff
  - New.Parameters
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Existence, choice and data

A mathematician writes "there is an $x$ with $P(x)$; fix such an $x$" and goes on. In Lean the two halves of that sentence are different acts. The first is a proposition. The second makes a datum, and Lean makes a datum out of a proposition only through the axiom of choice. Many objects of the source are made in this way: the source has 307 lines with `.choose` or `Classical.epsilon` (finding F-041). This section explains what such an object is, and what a reader may and may not assume about it. It also explains the other ways in which the source carries data: units, structures and classes.

### A proof of existence is not a datum

A proof of `∃ x, P x` is a term of a proposition. Lean treats two proofs of one proposition as equal. So a proof does not remember its witness in a form that a definition can use. Inside a proof of another proposition, the witness is available. The tactic `obtain ⟨x, hx⟩ := h` takes a proof `h` of `∃ x, P x` and gives a name `x` to a witness and a name `hx` to a proof of `P x`. This is the mathematician's "fix such an $x$", and it is allowed because the goal is a proposition.

**Lemma.** Let $N \geq 1$ and let $\chi$ be a Dirichlet character modulo $N$. Then there are $M \mid N$ with $M \neq 0$ and a primitive character $\psi$ modulo $M$ that induces $\chi$.

Lean: `New.exists_isPrimitive_changeLevel_eq` (Lib/Analytic/ZeroSymmetry.lean).

```lean
lemma New.exists_isPrimitive_changeLevel_eq :
    ∃ (M : ℕ) (hM : M ∣ N) (ψ : DirichletCharacter ℂ M),
      NeZero M ∧ IsPrimitive ψ ∧ changeLevel hM ψ = χ :=
  ⟨χ.conductor, χ.conductor_dvd_level, χ.primitiveCharacter, ⟨χ.conductor_ne_zero⟩,
    χ.primitiveCharacter_isPrimitive, χ.changeLevel_primitiveCharacter⟩
```

The statement binds a proof `hM : M ∣ N` inside the existence, because the induced character `changeLevel hM ψ` needs this proof as an argument. The proof is a term in angle brackets: the witnesses (the conductor, the proof that it divides $N$, the primitive character), then the proofs of the three properties. Mathlib has the primitive character as a datum, `χ.primitiveCharacter`. The lemma keeps only the fact that one exists. The reflection lemma of Section 1 uses it as a proof should: its first line is `obtain ⟨M, hM, ψ, _, hψ, rfl⟩ := exists_isPrimitive_changeLevel_eq χ`. The pattern `rfl` replaces $\chi$ by `changeLevel hM ψ` in the goal.

### Objects defined by choose

To define a datum from a proof of existence, the source uses `Classical.choose`. For `h : ∃ x, P x`, the term `h.choose` is an $x$, and `h.choose_spec` is a proof of `P h.choose`. Nothing else is known about `h.choose`. In particular it need not be the witness that the proof of `h` used. Lean does not unfold a theorem to find its witness.

**Theorem (Divisibility of the composite lift).** For admissible data $D$ there is a function $\mathrm{err} : \mathbb{N} \to \mathbb{R}$ with four properties. (a) $\mathrm{err}(p) \geq 0$ for every $p$. (b) If $p \neq N$, and $\chi_K(p) = 1$ or $x_1 \leq p$, then $\mathrm{err}(p) = 0$. (c) For every finite set $U$, $\sum_{p \in U} \mathrm{err}(p) \log p \leq \mathrm{errorUnit}$. (d) A $p$-adic statement: for every prime $p$ and every embedding of $\mathbb{C}$ in $\mathbb{C}_p$, the integral ramified source forms have a submodule of index dividing $p^l$, with $l \leq \mathrm{err}(p) \cdot \dim$, on which the composite lift has valuation at least $\mathrm{gain}(p) - \mathrm{err}(p)$, for all twists of level prime to $p$ and all chain data.

Lean: `New.Data.exists_err_gaugeLe_compositeLift` (New/UpperBound/Divisibility/LocalDivisibility.lean).

The head of the Lean statement and its first three clauses are these.

```lean
theorem exists_err_gaugeLe_compositeLift {P : Parameters} (D : Data P) :
    ∃ err : ℕ → ℝ,
      -- (a)
      (∀ p : ℕ, 0 ≤ err p) ∧
      -- (b)
      (∀ p : ℕ, p ≠ D.N → chiK P.d p = 1 ∨ D.x₁ ≤ p → err p = 0) ∧
      -- (c)
      (∀ U : Finset ℕ, ∑ p ∈ U, err p * log p ≤ D.errorUnit) ∧
```

The proof starts with `refine ⟨D.allowedLoss, ...`: the witness is the function `New.Data.allowedLoss` of the size estimates. Its place in the argument, as an input of Theorem A, is in [the three theorems](/chapter/theorems-a-b-c/).

**Definition.** The divisibility error of $D$ is the function chosen by the theorem above.

Lean: `New.Data.divisibilityError` (New/Reduction/ShortAndEnough.lean).

```lean
def divisibilityError : ℕ → ℝ := D.exists_err_gaugeLe_compositeLift.choose
```

The lemmas next to it give its properties, one clause each:

```lean
lemma divisibilityError_nonneg (l : ℕ) : 0 ≤ D.divisibilityError l :=
  D.exists_err_gaugeLe_compositeLift.choose_spec.1 l
```

and `New.Data.divisibilityError_eq_zero` and `New.Data.sum_divisibilityError_mul_log_le` for (b) and (c). The suffix `.1` takes the first clause of the conjunction.

**Remark (Formalization).** The divisibility error is some function with the properties (a) to (d). It is not shown to be the function `New.Data.allowedLoss`, although the proof of existence uses that function. A reader may use (a) to (d) and nothing more. This is enough for the argument, because every later use of the error goes through the four lemmas. A statement about `D.divisibilityError` is a statement about every function with (a) to (d), and a reader who wants an explicit formula must read it from `New.Data.allowedLoss` and the proof, not from the statement. Risk R5 of the plan of this book applies here: a chosen object has only the properties that are stated next to it.

### Units

The type `ℂˣ` is the group of units of $\mathbb{C}$, that is $\mathbb{C}^\times$. An element `c : ℂˣ` is a structure that holds a complex number `c.val`, its inverse, and the proofs that their products are $1$. The coercion `(c : ℂ)` is `c.val`. So a statement `∃ c : ℂˣ, ...` gives a nonzero number without a separate hypothesis $c \neq 0$. The inverse `c⁻¹` is the inverse in the group, a unit again, and it is not a junk value.

**Definition.** The seesaw constant $c_{\mathrm{ss}}$ of the data is the unit chosen by [Theorem](/decl/New.Data.seesaw_identity/) of Section 3, for the linear form `D.besselForm` and the archimedean point `D.besselPoint`.

Lean: `New.Data.seesawConst` (New/Reduction/ShortAndEnough.lean).

```lean
def seesawConst : ℂˣ := (D.seesaw_identity D.besselForm D.besselPoint).choose
```

The next definition of the file uses it: `(D.seesawConst⁻¹ : ℂˣ).val • D.ramifiedSourceForms.subtype` is the inclusion of the ramified source forms times the complex number $c_{\mathrm{ss}}^{-1}$. Here `•` is the scalar multiple of a linear map.

**Remark (Formalization).** The seesaw constant is a unit and so is nonzero, as its docstring says. It is chosen by `choose`, so it is some unit for which the identity holds. Section 3 shows that the identity can hold with both sides $0$. So the nonvanishing of the constant does not give the nonvanishing of the lower chain (findings F-068 and F-110).

### Objects defined by epsilon

The function `Classical.epsilon` is a second form of choice. For a predicate `P` on a nonempty type, `Classical.epsilon P` is an element that satisfies `P` if some element does, and an unspecified element otherwise. The lemma `Classical.epsilon_spec` (Mathlib) gives the property from a proof of existence. Unlike `choose`, the definition does not need the proof of existence. So the object always exists, and the existence is a hypothesis of the lemma that gives its property.

**Definition.** Let a group $H$ with a measure $\nu$ act on a measurable space $X$. A cutoff is a measurable $\beta : X \to [0, \infty]$ with $\int_H \beta(hx)\,d\nu(h) = 1$ for every $x \in X$. The chosen cutoff is `Classical.epsilon` of this predicate.

Lean: `New.chosenCutoff`, `New.IsCutoff` (Lib/Adelic/QuotientMeasure/Basic.lean).

```lean
def IsCutoff (β : X → ENNReal) : Prop := Measurable β ∧ ∀ x : X, ∫⁻ h : H, β (h • x) ∂ν = 1
```

```lean
noncomputable abbrev chosenCutoff : X → ENNReal := Classical.epsilon (IsCutoff ν)
```

**Remark (Formalization).** The docstring says that the chosen cutoff "is a cutoff when the action has one (`New.isCutoff_chosenCutoff`); otherwise it is an unspecified function." The lemma `New.isCutoff_chosenCutoff` has the hypothesis `[h_cutoff : HasCutoff ν X]`, a class that holds a proof that a cutoff exists. A reader who sees `chosenCutoff ν` in a statement must check that this instance is in scope, or the statement is about an unspecified function.

### Irreducible definitions

A definition marked `@[irreducible]` is one that Lean does not unfold when it checks that two terms are equal by definition. The proofs use a lemma about it instead. This changes how proofs work, and it does not change what the definition means.

**Definition.** For a class $c$ of a filling, the class cutoff $\beta_c$ is the product of a cutoff chosen for the unipotent subgroup of the class and the reduced indicator.

Lean: `New.Filling.classCutoff` (New/Spanning/Unfolding/Setup.lean).

```lean
@[irreducible]
def classCutoff (c : S.Classes) : (InfinitePlace E → 𝔰.G₁) → ENNReal :=
  (S.exists_cutoff_classUnipotent ((S.classUnipotent₀ c).subgroupOf (S.classUnipotent c))).choose *
    S.reducedIndicator
```

The lemma `New.Filling.exists_classCutoff_eq_mul` of the same file states the property: there is a measurable $\beta$ with $\beta_c = \beta \cdot \mathrm{reducedIndicator}$ and `∑' u : ..., β (S.ratToInf u * y) = 1` for every point $y$, the sum over the unipotent subgroup of the class. Its proof opens the definition once with `rw [classCutoff]`. Here the sum `∑'` is a sum in $[0, \infty]$, so it has its classical value (Section 3). The source has $15$ definitions marked irreducible. A reader can read each one as an ordinary definition.

### Structures and classes

A structure is a type of tuples with named fields. A field can be a number, a function, or a proof. The fixed parameters of the argument are a structure.

**Definition (Parameters).** A set of parameters is a pair of natural numbers $q_0$ and $d$ with $18480 \mid q_0$, $d$ prime, and $q_0 \mid 2(d + 1)$, $q_0 \nmid d + 1$.

Lean: `New.Parameters` (New/Reduction/Data/FieldsAndPlaces.lean).

```lean
@[local grind]
structure New.Parameters where
  /-- The modulus `q₀`. -/
  q₀ : ℕ
  /-- The prime `d` with `K = ℚ(√-d)`. -/
  d : ℕ
  /-- `q₀` is a multiple of `18480 = 16 · 3 · 5 · 7 · 11`. -/
  dvd_q₀ : 18480 ∣ q₀
  /-- `d` is prime. -/
  d_prime : d.Prime
  /-- `d ≡ q₀/2 - 1 mod q₀`, stated as: `q₀` divides `2 (d + 1)` but not `d + 1`. -/
  q₀_dvd_and_not_dvd : q₀ ∣ 2 * (d + 1) ∧ ¬q₀ ∣ d + 1
```

A term `P : Parameters` holds the five fields, and `P.q₀` is the first. The data of the argument are the structure `New.Data P`, with fields for the scales $x$, $x_1$, $b$, their logarithms, the sizes $m$ and $r$, and the inequalities between them. Its definition and its sizes are in [the data and its sizes](/chapter/data-and-sizes/). The source writes `variable {P : Parameters} (D : Data P)` at the top of most files of `New`, so most statements have these two hidden arguments.

A class is a structure that instance search fills in (Section 6). Some data of the source are classes, and so a statement does not name them. The class `Fact d.Prime` holds a proof that $d$ is prime. The classes `ThePrime p`, `PadicIso ℓ`, `CMType E` and `WeilData E` fix a prime, an isomorphism $\mathbb{C} \simeq \overline{\mathbb{Q}}_\ell$, a CM type and the data of the Weil representation. A statement with such an argument speaks about the instance in scope. The source also makes instances from facts: after the structure above it proves `instance : NeZero P.q₀ := ⟨by grind [zero_dvd_iff]⟩`, so that every statement about `P.q₀` gets $q_0 \neq 0$ without a hypothesis.

### What to take from this section

An `∃` in a hypothesis is used by `obtain` inside a proof. An object defined by `choose` or `epsilon` has only the properties of the lemmas next to it, and for `epsilon` only under the hypothesis of existence. A unit is a nonzero number by its type. A structure carries its numbers and its proofs together, and a class is a structure that the statement does not name.
