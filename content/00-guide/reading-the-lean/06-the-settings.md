---
title: The settings of the source
lean:
  - Lib/Speed.lean
  - Lib/Base.lean
  - New/Reduction/Data/Magnitudes.lean
  - New/Reduction/MainInequality.lean
  - New/Derivatives/Field/ChosenPlaces.lean
  - New/OneLift/ComparisonOperator/ProductsSpan.lean
  - New/OneLift/ComparisonOperator/GluingMaps.lean
decls:
  - New.isEmpty_iff_isVoid
  - New.Data.HasLogBound
  - New.Data.le_of_hasLogBound
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The settings of the source

Lean reads a file with many settings: how far to search for instances, which lemmas the simplifier uses, which definitions it may unfold, how long it may work. The source changes some of these settings. Most changes only make proofs faster or shorter. A few can change which hidden argument a statement gets. This section lists the settings, and for each it says what a reader of a statement must know. The short answer is that the settings change proofs and not statements, with two exceptions: instances, and the default proofs of hypotheses.

### The file of speed settings

The file `Lib/Speed.lean` is imported by `Lib/Base.lean`. The docstring of `Lib/Base.lean` says: "The other files of `Lib` and `New`, except `Lib.Speed`, import this file, directly or not, and with it the speed settings of `Lib.Speed`." So the settings of `Lib/Speed.lean` hold in every file of the development. The file `Statements.lean`, which states the theorems, imports only Mathlib, and so the settings do not touch the types of the five theorems. The docstring of `Lib/Speed.lean` is this.

> The three settings of this file make instance search and `simp` faster in all files of the development. They add no axiom, and no proof relies on them: with this file emptied, the other files still compile, more slowly.

The three settings are these.

1. Instance priorities. The line `attribute [instance 20]` lowers the priority of $84$ instances of Mathlib from the default $1000$ to $20$ (finding F-017). The comment says: "Instance search tries these instances late (the default priority is 1000). Tried early, they start long searches that fail."
2. A smaller simp set. The line `attribute [simp ←, simp]` tags $64$ lemmas of Mathlib in both directions. The comment of the file explains that this erases them from the default set of the simplifier, and that, unlike `attribute [-simp]`, the effect passes to every file that imports it (finding F-018). Among them are `tsum_empty`, `Nat.sub_eq_zero_of_le`, `CharP.cast_eq_zero` and `Nat.card_eq_zero_of_infinite`. A proof that needs one of them names it.
3. One new simp lemma, stated below.

**Lemma.** For every type $\alpha$, $\alpha$ is empty if and only if `IsVoid α` holds, where `IsVoid` is a synonym of `IsEmpty`.

Lean: `New.isEmpty_iff_isVoid` (Lib/Speed.lean).

```lean
def New.IsVoid : Sort* → Prop := IsEmpty
```

```lean
@[simp 1001]
lemma New.isEmpty_iff_isVoid (α : Sort*) : IsEmpty α ↔ IsVoid α := .rfl
```

The docstring says: "Many `simp` lemmas have a hypothesis `[IsEmpty α]`. When instance search does not find it, `simp` tries to prove it. This lemma ends the attempt at once." The simplifier rewrites `IsEmpty α` to `IsVoid α`, about which it knows nothing, and stops. The proof `.rfl` says that the two sides are equal by definition. For a reader the lemma means nothing: `IsVoid` occurs in no statement.

**Remark (Formalization).** The claim that the files still compile with `Lib/Speed.lean` emptied is in the docstring, in the README and in the GUIDE. The README says that it was checked on Lean 4.33.1. The file `lean-toolchain` pins Lean v4.35.0. So on the pinned version the claim is not checked (finding F-019, open). The claim does not bear on soundness. Lean checks each proof with the settings in force, and the kernel accepts or rejects it. It bears only on the statement that no proof relies on the settings.

### The options of the build

The file `lakefile.toml` sets options for every file. The option `autoImplicit = false` means that every variable of a statement is declared. Lean does not bind an unknown name silently as a new variable. For a reader this is a guarantee: each letter of a statement is either a declared argument or a defined constant. The options `maxHeartbeats = 4000000` (twenty times the default), `maxSynthPendingDepth = 3` and the thread stack `--tstack=400000` give Lean more room. They change nothing in a statement.

### Seal, irreducible and transparency

Lean checks that two terms are equal by definition by unfolding definitions. This can be slow. Three tools limit it.

1. A definition marked `@[irreducible]` is not unfolded (Section 4). The source has $15$ of them.
2. The command `seal f in` makes `f` irreducible for the next declaration only. The source has $135$ `seal` lines and $3$ `unseal` lines (finding F-020). A typical one is in `New/OneLift/ComparisonOperator/ProductsSpan.lean`, before the lemma `New.Rows.integral_mul_sum_choiceFn_eq_zero`: the comment `-- Keeps definitional checks from unfolding the finite sums.` and then `seal Finset.sum in`.
3. The option `set_option backward.isDefEq.respectTransparency false in` restores an older behaviour of the check of definitional equality, in which the check may unfold more than the current setting of transparency allows. It occurs $33$ times (finding F-021). An example is the gluing map in `New/OneLift/ComparisonOperator/GluingMaps.lean`, whose head is `@[simps -isSimp] def glue : FormTuples j →ₗ[ℂ] (D.descentPair ϑ j).FormV where`.

All three change how Lean checks a proof or builds a term. None of them changes a statement that is written in full. The type of `New.Rows.glue` is the type in its head, with or without the option. A reader can ignore them.

### Global and local instances

Instance search fills in the arguments in square brackets: `[NeZero N]`, `[Fact d.Prime]`, the ring structure of a type, a `Fintype` structure, a `DecidableEq` structure. The source adds instances of its own. It has $35$ lines of global `attribute [instance ...]` (one of them in `Lib/Speed.lean`), $83$ lines of `attribute [local instance ...]` and $3$ lines of `attribute [-instance ...]` (finding F-022). A global instance holds in every file that imports it. A local one holds to the end of its file or section.

This is the one place where a setting can change a statement. If two instances of one class exist and are not equal by definition, the statement means something different with each. For most classes this does no harm, because the class has at most one element up to equality. A `Fintype` structure on a type is unique, so a sum over a finite type has one value. A `DecidableEq` structure is unique, so an `if` has one value. A `NeZero` or `Fact` instance is a proof, and two proofs are equal. For a class that holds data, such as a module structure or a metric, the instance in scope matters, and the GUIDE says: "Local instances can matter for reading a statement."

The most common local instance in the source is this line:

```lean
attribute [local instance low] Fintype.ofFinite
```

It is in `New/Derivatives/Field/ChosenPlaces.lean` and in other files that sum over finite types (finding F-026). The function `Fintype.ofFinite` (Mathlib) makes a `Fintype` structure from a proof that a type is finite, by choice. With the line, a sum `∑ x : X, f x` makes sense for every finite type $X$, without a separate instance. Since all `Fintype` structures on a type are equal, the sum is the usual sum. The two structures need not be equal by definition, and a proof can need a step to identify them. That is a matter for the proof. A single proof can also make one locally: in `New/OneLift/TestedForms.lean` a proof has the line `have : Fintype (O.ChosenGL r) := Fintype.ofFinite _`.

### Sizes by instance search

The argument compares many sizes: products of powers of the scales $x$, $x_1$, $b$ and their logarithms. The source compares them by a class whose parameter Lean computes.

**Definition.** For data $D$, a sign $u$ and real numbers $F$ and $l$, the class `HasLogBound D u F l` holds the bound $|F| \leq e^{l}$ if $u$ is true, and the bound $e^{l} \leq F$ if $u$ is false.

Lean: `New.Data.HasLogBound` (New/Reduction/Data/Magnitudes.lean).

```lean
class HasLogBound (D : Data P) (u : Bool) (F : ℝ) (l : outParam ℝ) where
  /-- The upper bound `|F| ≤ exp l` if `u` is `true`, the lower bound `exp l ≤ F` otherwise. -/
  out : if u then |F| ≤ exp l else exp l ≤ F
```

The keyword `outParam` marks $l$ as an output of instance search: given $F$, Lean finds an instance and reads off an exponent $l$ (finding F-028). The instances follow the rules of arithmetic. One of them is the instance for the size $m$ with $m \in [\sqrt{x}, 2\sqrt{x}]$:

```lean
instance : HasLogBound D u D.m (D.logX / 2 + (if u then 2 else 0)) :=
  .of_mem_Icc (exp (D.logX / 2)) (2 * exp (D.logX / 2)) D.m_mem
    (by cases u <;> grind [D.scale_inequalities])
```

It gives $e^{(\log x)/2} \leq m$ and $m \leq e^{(\log x)/2 + 2}$, from $\sqrt{x} \leq m \leq 2\sqrt{x}$ and $2 \leq e^2$.

**Lemma.** For data $D$, let $|F| \leq e^{l}$ and $e^{l'} \leq G$, and let $l < l'$. Then $F \leq G$.

Lean: `New.Data.le_of_hasLogBound` (New/Reduction/Data/Magnitudes.lean), with `New.Data.lt_of_hasLogBound` for $F < G$.

The hypotheses are section variables, and the last one has a default proof:

```lean
variable [D.HasLogUpper F l] [D.HasLogLower G l'] [D.HasLogUpper A l] [D.HasLogLower B l']
  (h_exp : l < l' := by
    clear_aux_decl
    clear * - D
    repeat clear ‹_›
    grind (splits := 99) [D.scale_inequalities])
```

```lean
protected lemma le_of_hasLogBound : F ≤ G := (D.lt_of_hasLogBound h_exp).le
```

*Proof.* $F \leq |F| \leq e^{l} < e^{l'} \leq G$. $\square$

A hypothesis written `(h : P := by tac)` is a default argument. A caller who omits it gets the proof that the tactic `tac` finds. Here the tactic clears all hypotheses but $D$ and calls `grind`, an automatic prover for linear arithmetic and equalities, with the five scale inequalities of [the data and its sizes](/chapter/data-and-sizes/): $10^{12} C_P \leq \log\log b$, $100 \log\log b \leq \log x$, $10^{6}\log x \leq \log x_1$, $10^{6}\log x_1 \leq \log b$ and $6\log\log x_1 \leq \log\log b$, where $C_P$ is `P.constantBound`. The line `attribute [grind! .] le_constantBound r_odd m_even` gives `grind` three more facts: $C_P$ is at least each of $64$, $q_0$, $d$ and $\varphi(q_0)$, $r$ is odd, and $m$ is even.

So in `New/Reduction/MainInequality.lean` a line such as `have h_share : 4 / D.b ^ 2 ≤ 2⁻¹ := D.le_of_hasLogBound` is a complete proof of $4/b^2 \leq 1/2$. Instance search finds an upper exponent of $4/b^2$ and a lower exponent of $2^{-1}$, and `grind` proves that the first is smaller. The same file proves $|2\,\mathrm{err}| \leq f a \log^5 b$ by `have h_err : |2 * err| ≤ D.f * D.a * D.logB ^ 5 := D.le_of_hasLogBound`.

**Remark (Formalization).** For a reader of a statement, `HasLogBound` is a proof device. A statement that the source proves in this way is the plain inequality in its type, and a reader can read it so. Two points need care. First, the method compares exponents, so it proves only inequalities with room to spare, of the kind $A \leq B$ where $\log B - \log A$ is large compared with the errors in the exponents. An inequality that is tight cannot be proved this way. Second, in a lemma with an instance argument such as `[D.HasLogUpper F l]`, the exponent $l$ is a variable of the lemma. The lemma holds for every $l$ with the bound, and at each use instance search finds one $l$. A reader who wants to know which bound was used must find the instances that search applied.

### What to take from this section

The settings of `Lib/Speed.lean`, the options of the build, `seal`, `@[irreducible]` and the transparency option change how Lean finds proofs. They do not change a statement that is written in full. Instances can change a statement, but only for a class that holds data and has more than one element. Default arguments `(h : P := by tac)` are hypotheses, proved by a tactic when the caller omits them, and the statement still has them.
