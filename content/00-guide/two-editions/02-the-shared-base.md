---
title: The shared base
lean:
  - Statements.lean
  - Main.lean
decls:
  - DirichletLNonvanishingRightOfHalf
  - LFunction_ne_zero_of_half_lt_re
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The shared base

This section lists what the two editions have in common. The list is short, and it is exactly the part that a reader must trust. Everything below `Main.lean` differs between the editions, and the kernel checks it.

### The six files that are the same

The finding F-118 of the specification names six files that are the same byte for byte in the two editions. This book compared them again at the pinned commit 72fead1 with `cmp`, and it computed the SHA-256 digest of each. The table gives the size in bytes and the first twelve hexadecimal digits of the digest. Paths are relative to the folder of the edition.

| File | Bytes | SHA-256 (first 12 digits) | Content |
|---|---|---|---|
| `src/Statements.lean` | 783 | `79ef7ca776e4` | the four propositions of the source |
| `Challenge.lean` | 612 | `b729a3ccbc32` | the five theorems with `sorry`, for Comparator |
| `comparator.json` | 393 | `af227d4d6a09` | the setup of Comparator |
| `lakefile.toml` | 570 | `f36c58efd8ff` | the build targets and options |
| `lean-toolchain` | 25 | `ca5f1f601d34` | the Lean version, v4.35.0 |
| `lake-manifest.json` | 3220 | `1390a02c1729` | the Mathlib commit |

Two more files are the same byte for byte: `scripts/PrintAxioms.lean` (213 bytes), which prints the axioms of the five theorems, and `LICENSE`. The files `README.md`, `GUIDE.md` and `NOTICE` differ. The compact `NOTICE` has one more statement: its file `Lib/General/LinearAlgebra/Base.lean` restates about twenty matrix lemmas of Mathlib.

Each file of the table fixes one part of the meaning of the claim.

1. `Statements.lean` imports only Mathlib. It defines the four propositions `RiemannZetaZerosOnLine`, `DirichletLNonvanishingRightOfHalf`, `DirichletLZerosOnLine` and `PrimitiveDirichletLZerosOnLine`. The first theorem uses the proposition `RiemannHypothesis` of Mathlib. So the five types are the same in the two editions.
2. `lean-toolchain` and `lake-manifest.json` fix Lean v4.35.0 and Mathlib at commit 56a005855ea17e0b0958f73ec801ae140b0a1679. So the words `riemannZeta`, `DirichletCharacter.LFunction` and `RiemannHypothesis` in the statements refer to the same Mathlib definitions in the two editions.
3. `lakefile.toml` fixes the targets `Lib`, `New` and `Main`, and the options of the build: no automatic implicit arguments, a heartbeat limit of 4,000,000 and a larger thread stack. The options change what the elaborator can do in a given time. They do not change what the kernel accepts.
4. `Challenge.lean` and `comparator.json` set up the tool Comparator. The challenge states the five theorems with `sorry`. The configuration names the module `Main` as the solution, the five theorem names, the three permitted axioms `propext`, `Quot.sound` and `Classical.choice`, and the option `"enable_nanoda": true`.

### The proposition that the proof proves

Of the four propositions, one is the target of the main argument in both editions.

**Definition (The half-plane statement).** The *half-plane statement* is the proposition: for every integer $q \geq 1$, every Dirichlet character $\chi$ modulo $q$, and every $s \in \mathbb{C}$ with $\operatorname{Re} s > 1/2$, if $\chi \neq \chi_0$ or $s \neq 1$, then $L(s, \chi) \neq 0$.

Lean: `DirichletLNonvanishingRightOfHalf` (Statements.lean).

Here $\chi_0$ is the principal character modulo $q$, which Mathlib writes `1`, and $L(s, \chi)$ is Mathlib's `DirichletCharacter.LFunction`. [The half-plane and the line](/chapter/half-plane-to-line/) explains the statement and its relation to the other three.

**Theorem (The generalized Riemann hypothesis, half-plane form).** The half-plane statement holds.

Lean: `LFunction_ne_zero_of_half_lt_re` (Main.lean).

*Proof.* The source proves the theorem by the term `New.grh`. In each edition, `New.grh` is a declaration of the folder `New` of that edition. Section 3 states it and follows its proof in both editions. $\square$

**Remark (Formalization).** The name `New.grh` occurs in both editions, with the same type, but it names two different declarations: one in `grh/src/New/Reduction/OneSidedBound.lean` (line 239), one in `grh-compact/src/New/Main.lean` (line 174). The same is true of `New.zeros_on_line` and `New.zeta_zeros_on_line`. In the readable edition these three names are in the namespace `New`. In the compact edition they are written with the prefix `New.` in a file whose other declarations are mostly in the root namespace. A search for a name must say which tree it searches.

### The file Main.lean

`Main.lean` is not in the list of F-118, since its two versions differ. This book compared them with `diff`. The theorem names, the types and the proof terms are the same. The two differences are these.

1. The readable `Main.lean` has a docstring on each of the five theorems. The compact `Main.lean` has none.
2. Both files have the comment line "The proof is Levent Alpöge's, with Claude." and the one import `import New.Main`. The readable file puts the comment before the import, and the compact file puts it after the import.

F-118 says that `Main.lean` "differs only in docstrings and the order of imports". There is only one import. The order that differs is the order of the comment and the import. Neither difference changes a declaration. The five proof terms in both files are

- `riemannHypothesis := New.zeta_zeros_on_line New.grh`,
- `riemannZeta_eq_zero_re := riemannHypothesis`,
- `LFunction_ne_zero_of_half_lt_re := New.grh`,
- `LFunction_eq_zero_re := New.zeros_on_line New.grh`,
- `LFunction_eq_zero_re_of_isPrimitive := fun N _ χ _ ↦ LFunction_eq_zero_re N χ`.

So the deduction of the five theorems from the half-plane theorem has the same shape in both editions. The lemmas `New.zeros_on_line` and `New.zeta_zeros_on_line` take the half-plane statement as a hypothesis in both editions. The compact edition proves each of them with one call of the tactic `grind`. The readable edition gives longer proofs through the reflection of zeros. [The half-plane and the line](/chapter/half-plane-to-line/) explains the readable proofs.

### What the shared base implies

A reader who trusts the result of the source must trust three things: that `Statements.lean` and the statements in `Main.lean` say what they should say, that the axioms are the three standard axioms of Lean and Mathlib, and that the reported checks were done. The first two are the same in the two editions. The third is not the same.

The readable README reports these checks: a build without errors or `sorry`; the axiom list; an export by `leanexport` of the five theorems with all their dependencies, which the independent checkers nanoda, con-leche and con-ron accept; and a run of Comparator. The compact README reports a build without errors or `sorry`, a replay "through the kernel of Lean", the axiom list, and a run of Comparator. It does not name `leanexport`, nanoda, con-leche or con-ron (F-115). The file `comparator.json` of the compact edition has the option `"enable_nanoda": true`, as the readable one does. So a Comparator run on the compact folder, as configured, uses nanoda too. But the compact README does not report a separate check by nanoda.

**Remark.** The shared base makes the two editions comparable at the level of statements. It does not make them dependent. Neither edition imports a file of the other. A defect in a definition of one edition is not a defect of the other, unless both have it. A defect in `Statements.lean` would affect both, and so would a defect in the pinned Lean or Mathlib. These are the parts that a second edition cannot test. [What a kernel check guarantees](/chapter/claim-and-status/) discusses what remains to trust.
