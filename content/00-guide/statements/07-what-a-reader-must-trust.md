---
title: What a reader must trust
lean:
  - Statements.lean
  - Main.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What a reader must trust

This section collects the results of the chapter. It lists, for each statement, the objects of Mathlib that it uses, its classical form and the gaps between the two. Then it lists what a reader must trust to accept the claim of the source, and what the checks of the source do not cover. It ends with the entries of the register of findings that concern the statements.

### The statements at a glance

| Lean statement | Objects of Mathlib | Classical form | Gaps |
|---|---|---|---|
| `RiemannHypothesis` | `riemannZeta`, `Complex.re` | Riemann hypothesis, all of $\mathbb{C}$ | junk value at $1$, excluded; $\zeta(0) = -1/2$ by an update |
| `RiemannZetaZerosOnLine` | the same | the same | equal to the line above by definition |
| `DirichletLNonvanishingRightOfHalf` | `DirichletCharacter`, `NeZero`, the character `1`, `DirichletCharacter.LFunction` | no zero of $L(s, \chi)$ in $\operatorname{Re} s > 1/2$ | junk value at $s = 1$ for $\chi = 1$, excluded |
| `DirichletLZerosOnLine` | the same, without `1` | GRH in the open strip, every $\chi$ | zeros of imprimitive $\chi$ on $\operatorname{Re} s = 0$, outside the strip |
| `PrimitiveDirichletLZerosOnLine` | the same, with `IsPrimitive` | GRH in the open strip, primitive $\chi$ | the hypothesis is not used in the proof |

Each gap in the last column is a point where Lean must give a value that the classical theory does not give, or where the classical theory has zeros that the conjecture does not speak about. In each case the statement excludes the point, or the point does not change the truth of the statement. Sections 2 to 5 give the arguments.

### The trusted base

The source says what a reader must read to trust the result (grh/GUIDE.md, line 7, and grh/README.md, line 22). With the readings of this chapter, the list is the following.

1. **The Lean kernel and three axioms.** The kernel checks that each proof term has its type. The axioms are `propext`, `Classical.choice` and `Quot.sound`. They are the standard axioms of Mathlib, and they give classical logic and quotient types.
2. **The definitions of Mathlib that the statements use.** These are the objects in the table above, and the objects that they use in turn.
3. **The 16 lines of Statements.lean.** They define the four propositions. The file imports only Mathlib.
4. **The five statements of Main.lean.** They are the types of the five theorems. A reader must check that each theorem has the type of the claim, and that the file does not state a different proposition under a similar name.

Nothing else is in the base. The 300,000 lines of the proof, the files of `Lib` and `New`, the settings in Lib/Speed.lean and all the definitions of the source are inside the proof. The kernel checks them, and their meaning does not enter the claim. A wrong definition inside the proof can make the proof fail. It cannot make the five types say something else.

### How the method of this chapter shrinks item 2

A reader can read item 2 in two ways. The first way unfolds each definition: Section 2 does this for $\zeta$, down to a Mellin transform of $\theta$. This needs trust in many definitions of Mathlib, for example `mellin`, `WeakFEPair`, `evenKernel`, `jacobiTheta₂` and `Function.update`.

The second way pins each function by theorems of Mathlib: the Dirichlet series on $\operatorname{Re} s > 1$, differentiability off the pole, and the identity theorem. These theorems are proofs, so the kernel checks them. Then the reader needs to trust only the definitions that occur in the statements of the pinning theorems. These are the complex numbers, `tsum`, the complex power `cpow`, `DifferentiableAt`, `ZMod`, `MulChar` and the junk conventions for $1/0$ and for a sum that does not converge. All of them are basic, and each one has its textbook meaning, with the junk values that Sections 2 and 4 name. A reader who trusts these few definitions and the kernel can trust that `riemannZeta` and `LFunction` are the classical functions, without reading their construction.

The theorems of Mathlib that this chapter uses are these: `zeta_eq_tsum_one_div_nat_cpow`, `differentiableAt_riemannZeta`, `riemannZeta_zero`, `riemannZeta_one`, `DirichletCharacter.LFunction_eq_LSeries`, `DirichletCharacter.differentiableAt_LFunction`, `DirichletCharacter.LFunction_modOne_eq`, `DirichletCharacter.LFunction_changeLevel`, `DirichletCharacter.LFunction_ne_zero_of_one_le_re`, `DirichletCharacter.LSeriesSummable_iff` and `LSeries.eq_zero_of_not_LSeriesSummable`. They are in Mathlib at the pinned commit. The chapter quotes their statements from the source text of Mathlib. It did not build Mathlib.

**Remark (Why the empty list of definitions is safe).** The file grh/comparator.json has an empty list `definition_names`. Comparator can compare named definitions of the challenge with those of the solution. Here there is nothing to compare. The challenge, grh/Challenge.lean, and the solution, Main.lean, both import the same module Statements.lean, so the four propositions are the same constants in both. A solution cannot bring its own copy of a proposition under the same name, because Lean does not allow a name to be defined twice in one environment.

**Remark (The only sorry).** The edition has `sorry` in one file only, grh/Challenge.lean, in the five theorems that Comparator uses as a template. Nothing imports this file, and `lake build` does not build it. A reader who searches the source for `sorry` finds these five and no others.

### What the checks do not cover

The checks that the source reports (Section 6) cover the question "does Lean accept these five terms at these five types, with these three axioms?". They do not cover the following.

- Whether the five types express the classical statements. That is the reading of this chapter, and the reader must do it or accept it.
- Whether the checks were run as the README says. The repository has no logs of the runs and no CI configuration. This book did not rerun them. [The claim and its status](/chapter/claim-and-status/) gives the state of the checks.
- Whether the sandbox of Comparator worked as its design intends. The source ran it with a stand-in for the sandbox and does not say what the stand-in was.
- Whether a mathematician can follow the argument. No person has read the proof, and no paper comes with it. The rest of this book explains the argument. Explaining it is not the same as checking it.

Lean accepts the five theorems, if the reported checks hold. This book does not claim more.

### The findings on the statements

The entries F-001, F-004 to F-007 and F-010 to F-016 of the [register of findings](/chapter/register-of-findings/) concern the statements and the trust in them. This chapter adds the following points to them, each with the section that gives the argument.

- The proof has passed machine checks only, and no mathematician has read it (Section 6 and the list above).
- The reported checks with nanoda, con-leche, con-ron and Comparator have no logs in the repository, and Comparator ran with a stand-in sandbox (Section 6).
- The empty list `definition_names` is safe, and the only `sorry` is in Challenge.lean (the two remarks above).
- `riemannHypothesis` has the type of Mathlib, and the zeta statement of the source is equal to it by definition (Section 2).
- The half-plane form covers every modulus $N \geq 1$ and every character, and it excludes only $\chi = 1$ at $s = 1$ (Section 5).
- The forms on the line say nothing for $\operatorname{Re} s \leq 0$, and the strip must be open because of the Euler factors of imprimitive characters (Sections 4 and 5).
- The two lemmas of New/Main.lean take the half-plane form as a hypothesis, so the passage from the half-plane to the line can be read alone (Section 6). That passage uses the convention of Mathlib that $\Gamma_{\mathbb{R}}$ and the gamma factor are $0$ at their poles, and the reflection $s \mapsto 1 - s$ of zeros, which is a lemma of the source, `New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero` in Lib/Analytic/ZeroSymmetry.lean, not of Mathlib.
- `New.grh` is stated with the constant of Statements.lean, and its proof fixes $q_0 = 18480q$ and $d_0 = 9240q - 1$ (Section 6).
- The primitivity hypothesis of the fifth theorem is not used (Section 6).

This chapter found no gap in the statements beyond these points. The register gives some line numbers for F-014 and F-015 that do not match the source: the gamma factor is used at New/Main.lean, lines 34 to 37 and 51 to 53, and the case $s = 1$ of `New.grh` is at New/Reduction/OneSidedBound.lean, lines 243 to 245.
