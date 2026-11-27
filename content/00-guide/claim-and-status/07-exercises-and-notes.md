---
title: Exercises
lean:
  - Statements.lean
  - Main.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** The line form of the source has the hypothesis $0 < \operatorname{Re} s < 1$. Replace it by $0 \leq \operatorname{Re} s < 1$. Show that the new statement is false. Use the principal character $\chi_0$ modulo $2$ and find a point $s$ with $\operatorname{Re} s = 0$ and $L(s, \chi_0) = 0$.

*Hint.* $L(s, \chi_0) = (1 - 2^{-s})\zeta(s)$. The factor $1 - 2^{-s}$ vanishes at $s = 2\pi i k / \log 2$ for every integer $k$. For $k \neq 0$, $\zeta(s)$ is finite there.

**Exercise 2.** In the half-plane form, drop the clause "$\chi \neq \chi_0$ or $s \neq 1$". The new statement says something about the value of Mathlib's L-function of a principal character at $s = 1$, a point where the classical function has a pole. Explain why the truth of the new statement depends on a convention of the library and not on mathematics. For the modulus $N = 1$, decide whether the new statement is true, with Mathlib's value $\zeta(1) = (\gamma - \log 4\pi)/2$.

*Hint.* For $N = 1$ the L-function is $\zeta$. Check the sign of $\gamma - \log 4\pi$ with $\gamma \approx 0.577$ and $\log 4\pi \approx 2.531$.

**Exercise 3.** The fifth theorem of the source has the hypothesis that $\chi$ is primitive, and its proof does not use it. Show in two lines that a theorem whose proof does not use a hypothesis is a special case of the theorem without it. Then explain why this is no cause for concern here, and say which of the classical conjectures of Section 2 is the stronger statement.

*Hint.* The classical route goes from primitive characters to all characters through the finite Euler product. The source goes the other way.

**Exercise 4.** Write the list of what a reader must trust for the first theorem alone, the Riemann hypothesis in Mathlib's form. Which items of the list of Section 5 can you drop? Which file of the source is then no longer on the list?

*Hint.* The type `RiemannHypothesis` is a definition of Mathlib. The proof still passes through the half-plane form, but a proof is not trusted.

**Exercise 5.** Suppose that a later commit of the source moved the file of statements so that it imported `Lib/Speed`. Which of the conditions of Section 5 would a reader then have to check again, and what would they look for in `Lib/Speed`? Could the change make the kernel accept a false proof?

*Hint.* The settings change instance priorities and the simplifier. Ask whether the elaboration of a type in the file of statements could pick a different instance, for example a different structure on $\mathbb{C}$ or on the characters.

**Exercise 6.** For each of the following sentences, say whether it is in the voice of the kernel, of the source, or of the book, and whether the book can state it without a condition. (a) "The proof has passed machine checks only." (b) "`riemannHypothesis` depends on axioms: [propext, Classical.choice, Quot.sound]." (c) "The third theorem is equivalent to the fourth, by the functional equation." (d) "Theorem B gives enough forms."

*Hint.* (a) is a quotation of the root README. (b) is the expected output of a check, quoted by the source; no output is in the repository. (c) is classical mathematics. (d) is a summary of a Lean statement by its name.

**Exercise 7.** Find in the source the one file that contains `sorry`. Read it, and explain why its `sorry` does not weaken the claim. What would change if a file of `New` imported it?

*Hint.* It is the challenge of Comparator. If a proof file imported it and used one of its theorems, the list of axioms of the five theorems would contain `sorryAx`.

## Notes and references

The Riemann hypothesis is in Riemann's memoir of 1859. Davenport, *Multiplicative Number Theory*, Chapter 8, gives the memoir with proofs, and Chapter 9 gives the functional equation of $L(s, \chi)$ for a primitive character and its trivial zeros. Iwaniec and Kowalski, *Analytic Number Theory*, Chapter 5, set out the classical theory of L-functions in general, and the generalized Riemann hypothesis for that class. The factorization of the Dedekind zeta function of an abelian field into Dirichlet L-functions is in Washington, *Introduction to Cyclotomic Fields*, Chapter 4.

The design of Lean 4, with a small kernel that checks each declaration, is described by de Moura and Ullrich, *The Lean 4 Theorem Prover and Programming Language*, in the proceedings of CADE 28 (2021). The type theory of the kernel, with a model in set theory, is in Carneiro, *The Type Theory of Lean*, master's thesis, Carnegie Mellon University, 2019. Mathlib is described in The mathlib Community, *The Lean Mathematical Library*, in the proceedings of CPP 2020. Hales, *Formal Proof*, Notices of the American Mathematical Society 55 (2008), no. 11, discusses what a formal proof does and does not establish, and the role of the statement and of the kernel in it.

The facts about the source in this chapter come from its documents at the pinned commit: the root `README.md`, `grh/README.md`, `grh/NOTICE`, `grh/GUIDE.md`, `grh/REFERENCES.md`, `grh-compact/README.md` and `grh-compact/GUIDE.md`, and the files `grh/Challenge.lean`, `grh/comparator.json` and `grh/scripts/PrintAxioms.lean`. The text searches that the chapter reports were run on `grh/src` at the pin. No build was run.

The facts about the original proof come from four public documents, read on 27 November 2026: the note of Alpöge at `https://alpo.ge/remark.pdf` (four pages, made on 20 November 2026), the Lean archive of its footnote 1 at `https://alpo.ge/lean.tar.gz.part01` to `part14` (listed, and five small folders read, not built), the joint statement of the Lean FRO and the Mathlib Initiative at `https://leanprover-community.github.io/blog/posts/riemann-hypothesis/` (21 November 2026), and the working draft *The Alpöge-Claude proof of the Riemann hypothesis explained for the Riemann zeta function* at `https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/zeta-paper.pdf` (21 November 2026), of which pages 1 to 25 and 53 to 56 were read. The pages of checks by Andrew Sutherland are at `https://math.mit.edu/~drew/grh/` and `https://math.mit.edu/~drew/shortgrh/`. The classical lemma of Landau on Dirichlet integrals with coefficients of one sign is Lemma 15.1 of Montgomery and Vaughan, *Multiplicative Number Theory I*. Stepanov's method for curves over finite fields, which the note names as the model of the method, is in Bombieri, *Counting points on curves over finite fields (d'après S. A. Stepanov)*, Séminaire Bourbaki, exposé 430 (1973).

This chapter treats the findings of the register on trust: the status of the proof, its authorship, the pointer to the original method (now read, in Section 3), the missing logs, the stand-in for the sandbox, the empty list of definitions of Comparator, the single `sorry`, and the unused declarations. [The register of findings](/chapter/register-of-findings/) lists each of them with its status. The empty list of definitions is explained here by the reading of the configuration only. A person must still confirm it with the documents of Comparator.

Status: drafted by a model. No person has checked this chapter against the source.
