---
title: Checks, trust and the two editions
lean:
  - Main.lean
  - Statements.lean
  - New/Main.lean
  - New/Reduction/OneSidedBound.lean
  - Lib/Analytic/ZeroSymmetry.lean
  - New/Reduction/Zeros/PrimeError.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Checks, trust and the two editions

This section has the findings on the claim itself. The first table is about the evidence for the checks and about who wrote the documents. The second table is about the five trusted statements and how they relate to Mathlib. The third table is about the two editions of the source. The chapter [the claim and its status](/chapter/claim-and-status/) explains the first group in full, and [the statements](/chapter/statements/) explains the second.

The general rule of this section is simple. The source says that several programs checked it. The repository contains the inputs of those checks, but no output of any of them. So the book reports each check as a claim of the source, and a person must rerun it before the book can report it as done.

### The checks and the documents

| ID | File and line | Finding | Effect on the meaning | Chapter |
|---|---|---|---|---|
| F-001, explained | root `README.md:33-34` | The proof has passed machine checks only. The README says that no mathematician has read it and that no paper comes with it. | The mathematical claim rests on the Lean kernel and on the faithfulness of the five statements. No human reading supports it yet. | [claim-and-status](/chapter/claim-and-status/) |
| F-002, explained | `grh/README.md:5-6`; root `README.md:9-11` | The proof is described as Alpöge's, with Claude. The edition README says that Claude wrote the Lean text and all documents. | Docstrings, file heads, `GUIDE.md` and `INDEX.md` are claims by the same author as the code. No person has reviewed them. | [claim-and-status](/chapter/claim-and-status/) |
| F-003, open, [issue 18](https://github.com/tamnd/grh-lean-handbook/issues/18) | `grh/README.md:10` | The edition is a shorter rewriting of Alpöge's Lean proof, and many steps use other arguments. The only pointer to the original is the file `remark.pdf` on the author's web page. | The book cannot name a human source for the method. The documents do not list the steps that differ from the original. | [claim-and-status](/chapter/claim-and-status/) |
| F-004, open, [issue 15](https://github.com/tamnd/grh-lean-handbook/issues/15), [issue 16](https://github.com/tamnd/grh-lean-handbook/issues/16) | `grh/README.md:28` | The README claims an export by `leanexport` that the independent checkers nanoda, con-leche and con-ron accept. The repository has no logs of these runs. It has no folder `.github` and no CI, at the root or in `grh`. | A reader cannot see the output of any check. The book states the checks as claims until a person reruns them. | [claim-and-status](/chapter/claim-and-status/) |
| F-005, open, [issue 16](https://github.com/tamnd/grh-lean-handbook/issues/16) | `grh/README.md:30` | Comparator v4.35.0 was run "with a stand-in for its sandbox". The text does not say what the stand-in was. | The sandbox is part of what Comparator guarantees. Without it, the guarantee is not known in full. | [claim-and-status](/chapter/claim-and-status/) |
| F-006, explained | `grh/comparator.json`; `grh/README.md:22`; `grh/GUIDE.md:7` | The list `definition_names` is empty. The five theorem types use the four definitions of `Statements.lean`. The challenge and the solution import the same module `Statements`, so these definitions are the same constants. | The trusted base is `Statements.lean`, which imports only Mathlib, the five statements of `Main.lean`, and the list of axioms. A reader must read exactly these. | [statements](/chapter/statements/) |
| F-007, explained | `grh/Challenge.lean:8`, 11, 14, 17, 20 | The only `sorry` of the edition is in `Challenge.lean`, once for each of the five statements. No file imports it, and `lake build` does not build it. No file of `grh/src` contains `sorry`. | A reader who searches for `sorry` must not be alarmed by this file. The axiom check of issue 15 is the real test. | [claim-and-status](/chapter/claim-and-status/) |
| F-008, open | `grh/README.md:28` | The README says that several hundred of the more than 20,000 declarations are not used by the five theorems. No list of them exists. | A writer can explain dead code by mistake. A dependency closure of the five theorems would settle which declarations count. | [claim-and-status](/chapter/claim-and-status/) |
| F-009, explained | `grh/INDEX.md:5` | The sorting of results into `Lib` (known mathematics) and `New` (the argument) is called "a working classification". | A file in `Lib` is not evidence that the literature has the result in that form. | [how-to-read](/chapter/how-to-read/) |

### The five statements

| ID | File and line | Finding | Effect on the meaning | Chapter |
|---|---|---|---|---|
| F-010, explained | [Main.lean:5](lean:Main.lean#L5), 8, 21-22; [Statements.lean:3](lean:Statements.lean#L3)-4 | `riemannHypothesis` has the type `RiemannHypothesis` of Mathlib. `riemannZeta_eq_zero_re` is proved by the same term, so `RiemannZetaZerosOnLine` is the statement of Mathlib up to unfolding. The primitive form is proved from the general one, and its hypothesis `χ.IsPrimitive` is not used. | The statement of the Riemann hypothesis is not a private definition. The primitive form is a special case, not an extra result. | [statements](/chapter/statements/) |
| F-011, explained | [Statements.lean:6](lean:Statements.lean#L6)-8 | The half-plane form covers every modulus $N$ with `NeZero N` and every character. It excludes only $\chi = 1$ at $s = 1$. Modulus $1$ gives the zeta function. | Mathlib gives the L-function a junk value at the pole. The exclusion is needed, and it is the only one. | [statements](/chapter/statements/) |
| F-012, explained | [Statements.lean:10](lean:Statements.lean#L10)-12; `grh/README.md:22` | The form on the line speaks only of zeros with $0 < \operatorname{re} s < 1$. It says nothing for $\operatorname{re} s \leq 0$. | For an imprimitive $\chi$, the Euler factors give zeros on $\operatorname{re} s = 0$. So the strip must be open. | [statements](/chapter/statements/) |
| F-013, explained | [New/Main.lean:21](lean:New/Main.lean#L21), 23 | The file has `variable (h : DirichletLNonvanishingRightOfHalf)` with `include h`. Its lemmas take the half-plane form as a hypothesis. | The passage from the half-plane to the line does not depend on the main proof. It can be read alone. | [half-plane-to-line](/chapter/half-plane-to-line/) |
| F-014, explained | [New/Main.lean:32](lean:New/Main.lean#L32)-34, 50 | The proof uses the convention of Mathlib that `Gammaℝ` and `gammaFactor` take the value $0$ at their poles. | A reader used to the textbook $\Gamma$ must check this convention at each use. | [dirichlet-l-functions](/chapter/dirichlet-l-functions/) |
| F-015, explained | [New/Reduction/OneSidedBound.lean:239](lean:New/Reduction/OneSidedBound.lean#L239)-244; line 5 | `New.grh` is stated with the trusted type, and the file imports `Statements` at line 5. It takes $q_0 = 18480\,q$ and $d_0 = 9240\,q - 1$ (lines 240-241). The case $\rho = 1$ is Dirichlet's theorem (lines 243-244). | These constants fix the whole set-up. No restatement sits between the proof and the trusted type. | [main-inequality](/chapter/main-inequality/) |
| F-016, explained | [Lib/Analytic/ZeroSymmetry.lean:55](lean:Lib/Analytic/ZeroSymmetry.lean#L55)-63 | The lemma `New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero` (line 61) gives the reflection $s \mapsto 1 - s$ of zeros for every character, also imprimitive, with $\operatorname{re} s \neq 0$ and $s \neq 1$. It keeps only the reflection, not the functional equation or the root number. | It is the only bridge from the half-plane to the line. The file does not say whether Mathlib has the result. | [dirichlet-l-functions](/chapter/dirichlet-l-functions/), [half-plane-to-line](/chapter/half-plane-to-line/) |

Two remarks on this table. First, F-015 and F-013 together say that the trusted type of the main theorem is used directly. The chapter [the main inequality and the end of the proof](/chapter/main-inequality/) follows `New.grh` from its statement to its last step. Second, the row F-016 is narrower than the plan of the book. The plan said that Mathlib lacks this reflection. The file does not say so, and the book does not repeat the claim.

### The two editions

The repository has two editions of the same proof. The book reads the readable edition `grh`. The compact edition `grh-compact` is shorter and has other names. The chapter [the two editions](/chapter/two-editions/) gives the full table of names. The rows below are the points where a reader who moves between the editions can make an error.

| ID | File and line | Finding | Effect on the meaning | Chapter |
|---|---|---|---|---|
| F-113, explained | `grh-compact/src/New/Main.lean:28`, 121, 150, 174, 176 | In the compact edition one file holds the comment on the spine of the proof (from line 28), `star_inequality` (line 121) and `New.grh` (line 174). The compact bound is $x^{8\varepsilon + 1/2 - 1}$ (line 150), with $\varepsilon = (\min(\operatorname{re}\rho, 1) - 1/2)/51$ (line 176). | The two editions have different layouts and different exponents. A size from one edition is not a size of the other. | [two-editions](/chapter/two-editions/) |
| F-114, explained | `grh-compact/src/New/Main.lean:153`; `grh-compact/src/New/Endgame/OneSidedCriterion.lean:73`; [New/Reduction/OneSidedBound.lean:4](lean:New/Reduction/OneSidedBound.lean#L4) | The compact edition uses a window argument, `IsPolar.exists_window_sub_mul_le`, and has no folder for the prime number theorem. The readable edition imports `Zeros/PrimeNumberTheorem` and has `Lib/Analytic/PrimeNumberTheorem`. | One step is proved by different arguments in the two editions. | [two-editions](/chapter/two-editions/), [main-inequality](/chapter/main-inequality/) |
| F-115, explained | `grh-compact/README.md:28`, 30 | The compact README claims compilation, a replay in the kernel, and a run of Comparator. It does not name `leanexport`, nanoda, con-leche or con-ron. | The claimed checks differ between the editions. The claims of F-004 are made for the readable edition only. | [two-editions](/chapter/two-editions/) |
| F-116, explained | `grh-compact/README.md:36`; `grh-compact/src/Lib/General/LinearAlgebra/Base.lean:9-10` | The settings of the compact edition live in `Lib/General/LinearAlgebra/Base.lean`, with classical decidability. `IsVoid` is in the root namespace there, and in the namespace `New` in the readable edition. | Settings and names differ between the editions. | [two-editions](/chapter/two-editions/) |
| F-117, explained | `grh-compact/src`; `grh/src`; `grh-compact/src/New/Endgame/PrimeError.lean:38`; [New/Reduction/Zeros/PrimeError.lean:65](lean:New/Reduction/Zeros/PrimeError.lean#L65) | The compact edition has 573 files in `Lib` and 219 in `New`, with 112,827 lines in all. The readable edition has 495 and 306 files, with 477,124 lines. The compact name `primeError` is `primeRemainder` in the readable edition. | The compact edition has more and smaller files in `Lib`. A reader must map names between the editions. | [two-editions](/chapter/two-editions/) |
| F-118, explained | `Statements.lean`, `grh/Challenge.lean`, `grh/comparator.json`, `grh/lakefile.toml`, `grh/lean-toolchain`, `grh/lake-manifest.json` | These six files are the same byte for byte in both editions. `Main.lean` differs only in its docstrings and in the place of one comment line next to its single import. | The trusted base is the same in both editions. | [two-editions](/chapter/two-editions/) |
| F-130, explained | `grh-compact/src/Lib/Analytic/Landau/PolarLandau.lean:34-36` | The compact `IsPolar` has an extra clause: $(s - 1)\Phi(s)$ is analytic on $\operatorname{re} s \geq 1$. The readable `IsPolar` does not have it. | The two definitions of a polar function are not the same. A lemma about one does not apply to the other without a proof. | [two-editions](/chapter/two-editions/), [polar-functions](/chapter/polar-functions/) |

### What this section asks of a reader

The rows F-001 to F-009 say what kind of evidence supports the claim. They do not say that the evidence is weak or strong. They say that the outputs of the checks are not in the repository, and that the documents have one author, who also wrote the code. A reader who wants more than the claim must wait for issues 15 and 16, or run the checks.

The rows F-010 to F-016 say that the five statements are what they appear to be. Each uses the definitions of Mathlib, or the four short definitions of `Statements.lean`, and the passage from one form to another is short and can be read alone. This is the part of the source that a reader must read to trust the claim, if the reported checks hold.

The rows on the editions say that the two editions share the trusted base and differ in everything else. A reader who uses the compact edition to check a step of this book must use the name map of [the two editions](/chapter/two-editions/), and must not move a size or an exponent from one edition to the other.
