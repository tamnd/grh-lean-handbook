---
title: Two proofs of one statement
lean:
  - Main.lean
  - Statements.lean
  - New/Main.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Two proofs of one statement

The source repository has two folders of Lean, `grh/` and `grh-compact/`. Each folder is a complete Lean project. Each project builds the same five theorems, with the same names and the same types. The READMEs call the first folder the readable edition and the second folder the compact edition. This book follows the readable edition. Every `Lean:` line of the book names a declaration of `grh/`. This chapter explains the compact edition: what it is, what it shares with the readable edition, where its proof goes by a different route, and how its names map to the names of the book.

A reader meets the compact edition for three reasons. The first reason is size. The readable edition has about 300,000 lines of code, and the compact edition has about 76,000. A reader who wants to see the whole spine of the proof on a few screens reads the compact file `New/Main.lean`, which has 204 lines. The second reason is the comment at the head of that file. Its lines 27 to 115 list the inputs of the main inequality, the terms that cancel, the scales, and the error per dimension of each of Theorems A, B and C. The plan of this book calls it the best one-page summary of the error budget in the repository. The third reason is the claim itself. Two projects that prove the same proposition by partly different arguments give a reader two places to test the claim.

### The thesis of the chapter

The two editions are two proofs, not two layouts of one proof. They follow the same method, which the READMEs attribute to Levent Alpöge. Both READMEs say that "many steps are proved by other arguments" than in Alpöge's proof, and each README says that the other edition uses other arguments for some steps. This chapter finds such steps in the last part of the proof, where the main inequality turns into a bound for primes and then into the half-plane statement. It does not compare the two editions below Theorems A, B and C. There the folders of the two editions are cut in different ways, and a comparison file by file is a task for the volumes that explain those parts.

What the editions share is the trusted base. A reader who wants to know what Lean accepts reads three things: the file `Statements.lean`, the statements of the five theorems in `Main.lean`, and the list of axioms. Section 2 shows that these are the same in both editions, byte for byte or up to comments. So the two editions state the same five theorems. If the reported checks hold for each edition, then Lean accepts two proofs of the same five propositions.

### Why two proofs matter to a reader

In mathematics a second proof of a theorem is a test of the first. If the two proofs share a lemma, the test does not reach that lemma. If they differ at a step, a reader can compare the two routes, and an error in one route does not pass to the other. For Lean proofs the situation is different in one point. The kernel checks each proof. A second proof does not add confidence that a step is valid in Lean, since the kernel already checked it. It can help with other questions. Does the statement say what a reader thinks it says? Here the two editions do not help, since the statements are the same file. Do the definitions inside the proof have the meaning that the docstrings give them? Here a second edition helps, since the two editions often define the same object in two ways, and a reader can compare the two definitions.

The classical model is the prime number theorem. It has a proof by the zero-free region and contour integration, and a proof by a Tauberian theorem of Wiener and Ikehara. The two proofs share the facts that $\zeta(s)$ has a pole at $s = 1$ and no zero on the line $\operatorname{Re} s = 1$. They differ in the analytic step that turns these facts into an asymptotic formula. The two editions of the source are in a similar relation at one step. Both reduce the half-plane statement to a one-sided bound for a weighted sum over primes. The readable edition controls the remainder at the second cut-off $x_1$ by the prime number theorem in progressions with an error term. The compact edition does not use this theorem. It chooses $x_1$ by a window argument with moments of a Laplace transform. Section 4 explains both routes.

### The plan

Section 2 is about the shared base: the six files that are the same byte for byte, the file `Main.lean`, and what the shared base implies for trust. Section 3 follows the spine of the last part of the proof in both editions, from Theorems A, B and C to the half-plane theorem. It states each step in the form of the readable edition, with a `Lean:` line, and gives the compact form in a remark. Section 4 explains the two treatments of the second cut-off, with a model of the window argument and a complete proof of the model. Section 5 is the name map, in tables. Section 6 has the exercises and the notes.

A note on method. Every name in this chapter was found by a search in the source at the pinned commit. The names of the compact edition appear in tables, in prose and in remarks, not on `Lean:` lines. A compact name is marked with the folder, for example "compact `star_inequality`", where the readable name is the same or close.

This chapter explains what the source states and how the two editions prove it. It does not claim that either proof is correct. Lean accepts the five theorems of each edition if the checks that the source reports hold. This book did not rerun these checks ([the claim and its status](/chapter/claim-and-status/)).
