---
title: Finding a declaration and its proof
lean:
  - Main.lean
  - New/Reduction/ShortAndEnough.lean
  - New/Reduction/OneSidedBound.lean
  - New/Determinant/Twist/FitTwists.lean
decls:
  - New.Data.divisibilityError_eq_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Finding a declaration and its proof

Every statement of this book has a `Lean:` line with a full name and a file. This section explains how to go from such a line to the declaration in the source, how to read the names that occur inside a statement, and how to read a proof well enough to check a step. The source is large: about 300,000 lines of code in 801 files under `grh/src`, with 495 files in `Lib` and 306 in `New`, by its README. A reader needs a map and a few rules.

### The map

The source has four documents for readers, all in the folder `grh/`. The README gives the five theorems and the checks. The GUIDE gives the reading order, a glossary that turns the letters of the argument into Lean names, the sizes, the conventions and the settings. `CONTENTS.md` lists every file with its title. `INDEX.md` lists the results, with sources or related work and files. `REFERENCES.md` lists the citations and says which of them were compared with their sources.

Each file opens with a module docstring: a title, a summary of what the file proves, and often a section "Relation to the literature". The file `New/Main.lean`, for example, says under that heading: "Known result: the passage from the half-plane to the critical line by the functional equation." A reader who opens a file reads its head first.

The GUIDE says where to start: "To trust the result, read `Statements.lean`, the five statements of `Main.lean` and the list of axioms that `#print axioms` gives. All other definitions occur only inside the proof." This is the main rule of trust. The five theorems of `Main.lean` have types that are constants of Mathlib and of `Statements.lean`. The rest of the source is proof. A reader who checks a sentence of this book against the source checks the explanation, not the theorem.

### Names and namespaces

A full name is a path of components separated by dots: `New.Data.divisibilityError`. Both folders `Lib` and `New` use the namespace `New`. The exceptions are `Statements.lean`, `Main.lean`, and some lemmas in the namespaces of Mathlib, such as `star_mulVec_dotProduct` in `Lib/Base.lean`. The GUIDE says: "The names of the folder and of the namespace make no claim of novelty." A name under `New` can be a classical result.

A file sets the namespace with a block `namespace New.Data` ... `end New.Data`. Inside the block, a declaration `def divisibilityError` has the full name `New.Data.divisibilityError`. Some declarations give the full name in their head: `lemma New.zeros_on_line` in `New/Main.lean` is outside any namespace block. Some give a part: inside `namespace New.Data`, the head `noncomputable def CriticalPair.ratio` makes `New.Data.CriticalPair.ratio`. So to find a declaration from its full name, search for its last component after the word that introduces it.

**Example.** To find `New.grh`, search the folder `grh/src` for the text `theorem grh `. The search finds one line, `theorem grh : DirichletLNonvanishingRightOfHalf := by`, at line 239 of `New/Reduction/OneSidedBound.lean`, inside `namespace New`. To find `New.Data.divisibilityError`, search for `def divisibilityError`. The words that introduce a declaration are `def`, `abbrev`, `theorem`, `lemma`, `structure`, `class`, `instance` and `inductive`, with `noncomputable`, `protected` or `private` in front, or an attribute such as `@[simp]` or `@[irreducible]` on the line above.

### Dot notation

Inside a statement, names are short. If `D : Data P`, then `D.m` is `New.Data.m D`, the field $m$ of $D$, and `D.divisibilityError` is `New.Data.divisibilityError D`. Lean finds the namespace from the type of `D`. If `p : D.CriticalPair`, then `p.ratio ϑ` is `New.Data.CriticalPair.ratio p ϑ`. Dot notation also works for proofs: if `h : A ∧ B` then `h.1 : A` and `h.2 : B`, and if `h : 0 < x` then `h.ne'` is a proof of `x ≠ 0` by the Mathlib lemma `LT.lt.ne'` (Mathlib). The line `open ... in` and the `open` lines at the head of a file let a statement use short names from other namespaces. A name in an `open` line may also switch on scoped notation, as `open scoped ComplexOrder in` in Section 3.

**Lemma.** For admissible data $D$ and $l \in \mathbb{N}$ with $l \neq N$, and with $\chi_K(l) = 1$ or $x_1 \leq l$, the divisibility error at $l$ is $0$.

Lean: `New.Data.divisibilityError_eq_zero` (New/Reduction/ShortAndEnough.lean).

```lean
lemma divisibilityError_eq_zero {l : ℕ} (hN : l ≠ D.N) (hl : chiK P.d l = 1 ∨ D.x₁ ≤ l) :
    D.divisibilityError l = 0 := by
```

Read it with the rules of this section. The lemma is in `namespace New.Data`, so its full name is `New.Data.divisibilityError_eq_zero`. The arguments $P$ and $D$ come from the line `variable {P : Parameters} (D : Data P)` of the file. `D.N` is the level of the data, `D.x₁` the second cut-off, and `P.d` the prime of the parameters. The function `chiK P.d` is the quadratic character $\chi_K$.

*Proof.* This is clause (b) of [Theorem](/decl/New.Data.exists_err_gaugeLe_compositeLift/) of Section 4 for the chosen function. $\square$

### Reading a proof

A proof in tactics is a list of steps that change a goal. A reader does not need to follow every step. The steps that carry the mathematics are few, and the source writes a comment before most of them. These tactics occur most often.

1. `intro x h` names the next bound variable and hypothesis of the goal (Section 1).
2. `obtain ⟨x, hx⟩ := h` takes a witness from a proof of existence (Section 4), and `choose` makes functions from a proof of $\forall\exists$ (Section 5).
3. `have h : P := proof` proves an intermediate statement $P$ and names it. The text of `P` is the mathematical step.
4. `refine ⟨a, b, ?_⟩` gives part of a term and leaves the holes `?_` as new goals.
5. `calc a = b := ... _ ≤ c := ...` is a chain of equalities and inequalities, one step per line, as on paper.
6. `rw [lemma]` rewrites by an equation, and `simp [lemmas]` simplifies with the simp set and the named lemmas.
7. `linarith`, `nlinarith`, `positivity`, `omega`, `lia`, `grind` and `fun_prop` are automatic provers for linear arithmetic, nonlinear arithmetic, signs, integer arithmetic, general reasoning and properties of functions such as continuity and measurability.

**Example.** The proof of the reflection lemma of Section 1 starts with three steps, each with a comment. `obtain ⟨M, hM, ψ, _, hψ, rfl⟩ := exists_isPrimitive_changeLevel_eq χ` passes to the primitive character. Then a `have` proves `LFunction ψ s = 0` with the comment "`L(s, χ)` is `L(s, ψ)` times inverse Euler factors, which do not vanish at `s`." Then `refine or_iff_not_imp_left.2 fun gamma_ne ↦ ?_` turns the goal $A \vee B$ into: assume $\neg A$ and prove $B$. These three steps are the plan of the proof. The rest is the functional equation of the primitive character.

### From this book to the source and back

A `Lean:` line in this book has the form ``Lean: `Name` (path).``. The path is relative to `grh/src`. A link `[File.lean](lean:path#Lnn)` in a remark goes to line `nn` of a file at the pinned commit. The chapter [glossary and index of Lean names](/chapter/lean-index/) of this volume is made by the build from the `Lean:` lines, so it lists every name that has a statement in this book. A statement of the book says exactly what the Lean says. Where the classical object differs from the object of the source, the book gives both and a `**Remark (Formalization).**` on the difference.

To check that Lean accepts the proof, the README gives the commands: `lake exe cache get` and `lake build` with the pinned Lean and Mathlib, and `lake env lean scripts/PrintAxioms.lean` to list the axioms. The README says that the first of its five results is `'riemannHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]`. These are the three standard axioms of Mathlib. The README also reports that the independent checkers nanoda, con-leche and con-ron accept an export of the five theorems, and that the tool Comparator accepts the proofs against `Challenge.lean`. This book does not repeat these checks. It says "Lean accepts, if the reported checks hold".

### What to take from the search

A full name gives the file by a search for its last component. A short name inside a statement is resolved by the type of the object before the dot, and by the `namespace`, `variable` and `open` lines of the file. A proof is read by its comments, its `have` steps and its `calc` chains. The trust in the theorem rests on `Statements.lean`, the five statements of `Main.lean` and the axioms, not on the rest of the source.
