---
title: The reported checks
lean:
  - Main.lean
  - Statements.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The reported checks

This section lists each machine check that the documents of the source report. For each check it says what the check does, what it would show if it passed, what the repository holds as evidence, and how a reader can run it again. The summary is short. The documents report four kinds of check. The repository holds the files that set up the checks, and the text of the claims. It holds no output of any check: no log, no transcript, and no configuration of continuous integration. This book did not run any of the checks.

### The setting

A Lean project is built by the tool Lake. The project of the readable edition pins the Lean toolchain `leanprover/lean4:v4.35.0` (`grh/lean-toolchain`) and Mathlib at the commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (`grh/lakefile.toml`, line 16, and `grh/lake-manifest.json`). The manifest pins the other packages that Mathlib needs. So the build is reproducible in principle: the same source, toolchain and packages give the same result.

When Lean elaborates a file, it turns each declaration into a term of its type theory and passes the term to the kernel. The kernel is a small type checker. It adds the declaration to the environment only if the term has the stated type. So a build that succeeds has passed every declaration of every file through the kernel once. A tactic can fail or be slow, but it cannot add a declaration that the kernel rejects. This is the design that de Moura and Ullrich describe for Lean 4 (*The Lean 4 Theorem Prover and Programming Language*, CADE 28, 2021). The checks below are layers on top of this design. Each layer removes one kind of doubt that the layer below leaves.

### The build

The claim: "Every file in `src` compiles with the pinned Lean and Mathlib, without errors or `sorry`." (`grh/README.md`, line 28.)

What it would show: the kernel of Lean 4.35.0 accepted every declaration of the readable edition, and no proof is left open. In Lean, an open proof is written `sorry`. It is accepted with a warning, and it adds the axiom `sorryAx`. So "without `sorry`" is a claim about warnings and about axioms.

The evidence in the repository: none. The README gives the cost: "one to two hours on 12 cores", with "24 GB of memory" (`grh/README.md`, line 25), and about 85 minutes more if the cache of Mathlib is missing.

How to run it: in the folder `grh/`, run `lake exe cache get` and then `lake build`. The default targets are the libraries `Lib`, `New` and `Main` (`grh/lakefile.toml`, line 3).

A text search of the source at the pin finds no `sorry` in `grh/src`. The one `sorry` of the edition is in `grh/Challenge.lean`, which is not a default target and which nothing imports. That file is the challenge of Comparator, described below.

### The list of axioms

The claim: the five theorems "depend only on the three axioms" `propext`, `Classical.choice` and `Quot.sound` (`grh/README.md`, line 28). The README quotes the first line of the expected output: `'riemannHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]` (`grh/README.md`, line 25).

What it would show: the command `#print axioms` walks through every declaration that a theorem uses, down to the definitions of Mathlib, and lists every axiom that it meets. The three axioms are propositional extensionality, the axiom of choice in the form of Lean, and the soundness of quotients. Mathlib uses the same three. If any proof below the five theorems used `sorry`, the list would contain `sorryAx`. If any file declared a new axiom, the list would contain it. If a proof used the evaluation of compiled code, through `native_decide`, the list would contain `Lean.ofReduceBool`.

The evidence: the script `grh/scripts/PrintAxioms.lean`, of seven lines. It imports `Main` and prints the axioms of the five theorems. The expected output is quoted only in part, and no output is in the repository.

How to run it: after the build, `lake env lean scripts/PrintAxioms.lean`.

A text search at the pin finds no declaration `axiom` and no `native_decide` in `grh/src`. This is consistent with the claim, but it is not the check. Only the command, run on the built project, is the check.

### The independent checkers

The claim: "An export of the five theorems with all they depend on, Mathlib included (...), is accepted by the independent checkers nanoda, con-leche and con-ron." (`grh/README.md`, line 28.) The export is made by the tool `leanexport`, with the five theorem names.

What it would show: the export is a text file with every declaration that the five theorems use, Mathlib included, as terms of the type theory. An independent checker is a second implementation of the kernel, written apart from Lean. If three such programs accept the export, then a bug in the kernel of Lean alone cannot explain the acceptance. A bug would have to be in all four kernels. The check also removes a second doubt. The export is made from the environment after the build. A checker reads only the export. So it does not depend on any code that ran during the build.

The evidence: none. The repository has no export file, no output of the three programs, and no version numbers for them. The README of the compact edition does not report this check. It says instead that every file "was replayed through the kernel of Lean" (`grh-compact/README.md`, line 28). The README of the readable edition names the replay tool, `lake env leanchecker <module>`, as a way for a reader to replay a module (`grh/README.md`, line 25), but it does not report a run of it.

How to run it: the README gives the command of the export. A reader then runs each checker on the export file. The book has not tried this, and it cannot say how long it takes.

### Comparator

The claim: "We ran Comparator v4.35.0 on this folder (Linux, with a stand-in for its sandbox and `ulimit -s unlimited`), and it accepted the proofs; allow 64 GB of memory and a few hours." (`grh/README.md`, line 30.) The README of the compact edition has the same sentence (`grh-compact/README.md`, line 30).

What Comparator does: the README says that Comparator "compares them with `src/Main.lean` and checks the proofs again", where "them" are the five statements of `Challenge.lean`. The file `grh/Challenge.lean` imports only the file of statements, and states the five theorems with `sorry`. The file `grh/comparator.json` names `Challenge` as the challenge and `Main` as the solution, lists the five theorem names, lists the three permitted axioms, gives an empty list of definition names, and turns on nanoda as a second kernel.

What it would show: each of the five theorems has, in the solution, the same type as in the challenge; each uses only the three axioms; and the proofs pass the kernel of Lean and nanoda. The challenge imports only Mathlib and the 16 lines of the file of statements. So the comparison ties the five proved types to a file that a person can read in a few minutes, and that does not import the proof.

The sandbox: a build of a Lean project runs code. Tactics, elaborators and commands run while Lean reads a file. A tool that compares a challenge with an untrusted solution must assume that the solution can run hostile code during its build, for example code that changes the files of the challenge or the output of the comparison. A sandbox limits what that code can reach. The source ran Comparator "with a stand-in for its sandbox". It does not say what the stand-in was or what it allowed. So the guarantee of this run against hostile build code rests on a component that the documents do not describe.

Two facts make this gap smaller, but they do not close it. First, the check of an export by independent kernels, as claimed above, does not depend on code that ran in the build. Second, a text search of `grh/src` at the pin finds no `#eval`, no `run_cmd`, no new syntax or elaborator, and no import of the meta code of Lean. So the source does not, as text, contain its own code that runs at build time, apart from the tactics of Lean and Mathlib that it calls. A text search is a reading, not a proof, and it does not replace the sandbox.

The empty list of definitions: the challenge and the solution both import the same module `Statements`. So the four propositions in the five types are the same constants in both, and Comparator need not compare their definitions separately. This is how this book reads the configuration. The book has not confirmed it with the documents of Comparator.

The evidence: the files `Challenge.lean` and `comparator.json`. No output of the run.

### A summary

The four checks and their evidence, in one list:

1. **The build.** The claim is in `grh/README.md`, line 28. The repository holds the project files. It holds no log.
2. **The list of axioms.** The claim and part of the expected output are in `grh/README.md`, lines 25 and 28. The repository holds the script. It holds no output.
3. **The independent checkers.** The claim is in `grh/README.md`, line 28, for the readable edition only. The repository holds the command of the export, in the README. It holds no export and no output.
4. **Comparator.** The claim is in `grh/README.md`, line 30, and in the compact README. The repository holds the challenge and the configuration. It holds no output, and the stand-in for the sandbox is not described.

The README of the readable edition draws the limit of these checks itself: "These checks show that Lean accepts the proof of the stated theorems." (`grh/README.md`, line 28.) This book agrees with the limit, and goes one step further. The checks would show this if they passed. The repository has the claims that they passed, and no record of the runs. Issues of this book ask a person to rerun the build and the list of axioms at the pin and attach the log to a release ([issue 15](https://github.com/tamnd/grh-lean-handbook/issues/15)), and to ask the authors for the logs of the independent checkers and of Comparator, and for a description of the stand-in sandbox ([issue 16](https://github.com/tamnd/grh-lean-handbook/issues/16)).
