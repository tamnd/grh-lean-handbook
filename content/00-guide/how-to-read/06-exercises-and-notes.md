---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises of this chapter are exercises in reading the book. They need the chapters that they name, and a clone of the source at the pinned commit for Exercises 4 and 5.

**Exercise 1.** Take the chain of Section 2, with its six links. For each link from 2 to 6, name the chapter of Volume 1 that proves it, and the chapter of Volume 2 that gives its analytic background, if there is one.

*Hint.* Use the chapter map in [the map of the book](/chapter/theorem-and-plan/#the-map-of-the-book). The step from 2 to 3 is [the main inequality and the end of the proof](/chapter/main-inequality/), with the lattices of [twisted lattices](/chapter/twisted-lattices/). The step from 4 to 5 is [Landau's criterion](/chapter/landau-criterion/), with [Landau's theorem](/chapter/landau-theorem/) and [Pólya-Vinogradov and quadratic twists](/chapter/polya-vinogradov/) in Volume 2. The step from 5 to 6 is [from the half-plane to the line](/chapter/half-plane-to-line/), with [Dirichlet L-functions and zero symmetry](/chapter/dirichlet-l-functions/).

**Exercise 2.** A reader wants to judge only the claim that the error of the star inequality is small next to the main term $m \cdot \mathrm{rem}$. Using Sections 2 and 3, write the shortest list of chapters that this reader needs, and say which items of Path 1 the reader can skip.

*Hint.* The star inequality and its error budget are in [the main inequality and the end of the proof](/chapter/main-inequality/). Its errors come from Theorems A, B and C, as stated in [Theorems A, B and C](/chapter/theorems-a-b-c/), and from Hadamard's inequality in [twisted lattices](/chapter/twisted-lattices/). The sizes are in [the data and its sizes](/chapter/data-and-sizes/). The reflection of zeros and Landau's criterion are not needed.

**Exercise 3.** Path 2 for Theorem A and Path 2 for Theorem B share some background chapters. List the chapters of Volumes 4, 5 and 6 that both paths contain. Which chapter of Volume 6 is in all three of the paths for Theorems A, B and C? What does this suggest about the role of that chapter in the argument?

*Hint.* Compare the lists of Section 3 item by item. Read the plan of the shared chapter of Volume 6 in the plan of that volume, and the place where the opening chapter of each argument volume cites it.

**Exercise 4.** Open [from the half-plane to the line](/chapter/half-plane-to-line/) and the file Lib/Analytic/ZeroSymmetry.lean of the source. For the zero reflection theorem, find the Lean declaration named on its `Lean:` line. Compare its hypotheses with the hypotheses of the statement, one by one. Where in the proof of the book is each hypothesis used?

*Hint.* The theorem has three hypotheses on $s$, and the paragraph after its proof says where each is used. Check that the Lean conclusion is a disjunction, and that its first part is about the gamma factor of $\chi$, not of the primitive character that induces it.

**Exercise 5.** Choose one remark on the formalization in Volume 1 that concerns a junk value. Say which convention of Lean it uses ($x/0 = 0$, the value of a divergent sum, a value of a function at a pole, or truncated subtraction). Then say whether the statement above the remark would be false, true for a different reason, or unchanged, if the convention were replaced by the textbook one.

*Hint.* [Reading the Lean](/chapter/reading-the-lean/) lists the conventions. The remarks in [from the half-plane to the line](/chapter/half-plane-to-line/) on the value of $\zeta$ at $s = 1$ and on $\Gamma_{\mathbb{R}}$ at its poles are two good cases.

**Exercise 6.** A reader finds that a statement of a chapter has the hypothesis $x \geq 2$, while the Lean declaration on its `Lean:` line has no such hypothesis. Is this an error of the book? If so, what is its weight, and what must the report of Section 5 contain? What changes if the Lean declaration has the hypothesis and the book does not?

*Hint.* A statement must not add a hypothesis. An added hypothesis makes the statement weaker than the Lean statement, so the book claims less than the source proves. A missing hypothesis makes the statement stronger than the Lean statement, so the book claims more than the source proves. The second case is the more serious one.

## Notes and references

This chapter has no mathematical content of its own, and so no classical sources. Its rules come from the plan of the book, which is part of the repository of the book: the brief for a writer, `prompts/chapter.md`, gives the form of a chapter, and the brief for a checker, `prompts/review.md`, gives the meaning of the labels `checked` and `reviewed`.

The plan of the book names two graduate textbooks as models for the form and the level of a chapter: Iwaniec and Kowalski, *Analytic Number Theory*, and Bump, *Automorphic Forms and Representations*. The prerequisites of Section 1 are those of the plan. Davenport, *Multiplicative Number Theory*, treats Dirichlet's theorem in Chapters 1 to 4, primitive characters in Chapter 5, and the functional equations of $\zeta$ and of $L(s, \chi)$ in Chapters 8 and 9. Neukirch, *Algebraic Number Theory*, Chapters I to III, treats the algebraic integers, valuations, and Riemann-Roch theory over number fields.

A reader new to formal proofs can read [reading the Lean](/chapter/reading-the-lean/) before any other chapter of the Lean path. The book needs no Lean beyond what that chapter explains.

The reading paths of Section 3 refine the paths of the plan of the book. They differ from it in two points. The plan gives the path for Theorem A as Volume 3 on CM, Volume 4 chapters 1 and 2, and Volume 6 chapters 1 to 3. The opening chapter of Volume 9 names, in addition, two more chapters of Volume 4, three chapters of Volume 5 and the fourth chapter of Volume 6, and Section 3 follows it. The plan gives the path for Theorem B with Volume 5 chapters 1 to 3. The opening chapter of Volume 10 also uses the chapter on characters of $\mathrm{GL}_n$ over a finite field, which is chapter 5 of Volume 5. The plan gives the Lean path as chapters 5 to 8 of Volume 0. Section 3 adds chapters 2, 3, 9 and 10, which a Lean reader needs for the statements, the reported checks, the names of the compact edition and the index.

Status: drafted by a model. No person has checked this chapter.
