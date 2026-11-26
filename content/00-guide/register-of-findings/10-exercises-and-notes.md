---
title: Exercises and notes
lean:
  - New/Determinant/Twist/FitTwists.lean
  - New/UpperBound/Seesaw/SeesawIdentity.lean
  - Lib/DiscreteSeries/FlenstedJensen/Defs.lean
  - New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean
  - Lib/Analytic/ZeroSymmetry.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the register as a tool. Each one asks the reader to check a row against the source, or to write a new row. A reader needs a copy of the source at the pin and the commands `grep` and `sed`, or an editor with a search.

**Exercise 1.** Open `New/Determinant/Twist/FitTwists.lean` and find the definition of `RankOneIndex` and the field `hasLiftRank`. Count the elements of `RankOneIndex z` for $z = 5$, $z = 10$ and $z = 12$. Then decide whether the row F-038 states the bound correctly, and whether the docstring at line 119 of the same file says the same.

*Hint.* The type ends in `Fin (2 * z - 20)`, and the subtraction is in $\mathbb{N}$, so $2z - 20$ is $0$ for $z \leq 10$. The field asks the cardinality $2z$ and $2 \leq z$. Compare $20$ with $2z$ for the three values. The docstring states only the second condition (F-111).

**Exercise 2.** Let $X$ and $Y$ be complex vector spaces. Assume a theorem says: there is a unit $c$ with $L = c \cdot M$, for two linear maps $L, M : X \to Y$. Show that the theorem holds with $c = 1$ whenever $L = 0$ and $M = 0$. Then read the proof of `seesaw_identity` around [line 630](lean:New/UpperBound/Seesaw/SeesawIdentity.lean#L630) of `New/UpperBound/Seesaw/SeesawIdentity.lean`, and say in which case the proof uses this. Which row of the register records it, and why is that row open?

*Hint.* If $L = 0$ and $M = 0$, then $L = c \cdot M$ for every $c$. The comment of the proof says what happens when the natural constant $c_0 C / d$ is $0$. The row is F-068. It is open because the source does not show in this file where the nonvanishing of the lower chain comes from.

**Exercise 3.** The definition `weightMinors` of `Lib/DiscreteSeries/FlenstedJensen/Defs.lean` is a `finprod` of quotients by `det g`. Let $g$ be a singular matrix. Use the conventions of Mathlib for division by $0$ and for `finprod` to compute `weightMinors` at $g$, under the assumption that infinitely many factors are $0$. Then say whether this junk value can enter a statement about the formal degree.

*Hint.* For a singular $g$ each quotient is $x/0 = 0$. A `finprod` whose support (the set of factors different from $1$) is infinite is $1$ by convention. For the formal degree, look at where the source proves square integrability, which makes the integral finite and positive (F-034).

**Exercise 4.** Row F-087 says that the bound $2r + 2N + 3 < n$ is the explicit hypothesis `h_rank` of `stdClassSum_gramForm_eq_zero`. Find the theorem in `New/OneLift/FalseLifts/PeriodsOfFalseLifts.lean`, and check this. Then find the definition of `FitsParams`, and check that it does not contain the bound. What would a reader conclude about the stable range if the bound came through `FitsParams`, and why does it matter where it comes from?

*Hint.* Search for `theorem stdClassSum_gramForm_eq_zero` and read its binders. The bound is on `card r`, `card N` and `card n`. Search for `def FitsParams` or `structure FitsParams` in `New/UpperBound/Objects`. A hypothesis of a theorem must be proved at each call site, while a field of a structure is proved once, where the structure is built.

**Exercise 5.** Choose one row of Section 3 with the status open, for example F-023. Write a plan for a person who wants to close it. Say which files to read, what to search for, and what result would close the row as explained. Then write the new row as it would look after the check.

*Hint.* A global instance can enter a statement only through the files that import its file. A search for the class name in the statements of `New` gives the candidates. The row is explained if no statement of `New` elaborates with the instance in a way that differs from the instance of Mathlib, or if the row names each statement that does.

**Exercise 6.** A writer finds that the docstring of a lemma of the source says "for all primes $p$", while the lemma has the hypothesis `5 ≤ p`. Write the new row of the register. Give it a number, put it in the right table, and fill the five columns. Then say which existing row it is close to.

*Hint.* The new row takes the next free number after the largest number of the register, and it goes at the end of the table of docstrings in Section 8. Its status is explained if the Lean text settles the point. The row is close to F-088, which records the hypothesis $5 \leq p$ of `killsCokernel_of_isUnramified`.

**Exercise 7.** Read the lemma at [line 61](lean:Lib/Analytic/ZeroSymmetry.lean#L61) of `Lib/Analytic/ZeroSymmetry.lean`. State it in words. Then say why the row F-016 does not claim that Mathlib lacks the result, although the plan of the book said so.

*Hint.* The lemma says: if $L(s, \chi) = 0$, $\operatorname{re} s \neq 0$ and $s \neq 1$, then the gamma factor of $\chi$ is $0$ at $s$, or $L(1 - s, \chi^{-1}) = 0$. Read the head of the file and the docstring: a claim about what Mathlib lacks needs a statement in the source or a search of Mathlib at the pinned version, and the register states only what the source shows.

## Notes and references

The register is the one of the plan of this book, in the section on findings, with each row checked again against the readable edition of lsernau/grh-lean at commit 72fead1. The check confirmed most rows as they stood. It corrected the lines or the files of F-007, F-016, F-037, F-039, F-051, F-062, F-080, F-109, F-120, F-121 and F-122. It narrowed the claims of F-016 (the file does not say that Mathlib lacks the reflection), F-080 (five lemmas carry the hypothesis, not two) and F-087 (the bound is an explicit hypothesis, not a field of `FitsParams`). It dropped F-129, whose numerical claim about a residue at $s = 0$ the check could not confirm, since `IsPolar` speaks only of $\operatorname{re} s > 0$. The candidates F-123 to F-128 and F-131 to F-136 are corrections of the notes of the book, not facts about the source, and the chapter does not list them.

The documents of the source that the register cites are `grh/README.md`, `grh/GUIDE.md`, `grh/INDEX.md`, `grh/REFERENCES.md` and `grh/ATTRIBUTION.md`, and the root `README.md` of the repository. The file `grh/REFERENCES.md` reports the state of the citations of the source itself, and the rows F-100 and F-101 repeat its counts.

The conventions of Mathlib on junk values are explained in the documentation of Mathlib and in the chapter [reading the Lean](/chapter/reading-the-lean/) of this volume. The use of `Classical.choose` and `Classical.epsilon` is explained in J. Avigad, L. de Moura, S. Kong and S. Ullrich, *Theorem Proving in Lean 4*, in the chapter "Axioms and Computation". The checkers that the source names are the programs `leanexport`, nanoda, con-leche, con-ron and Comparator; the register does not describe them, and the chapter [the claim and its status](/chapter/claim-and-status/) says what each is claimed to check.

The four open checks are issues of the repository of this book: [issue 15](https://github.com/tamnd/grh-lean-handbook/issues/15) (rerun the build and the axiom check at the pin), [issue 16](https://github.com/tamnd/grh-lean-handbook/issues/16) (the logs of the independent kernels and of Comparator), [issue 17](https://github.com/tamnd/grh-lean-handbook/issues/17) (`Lib/Speed` on Lean 4.35.0) and [issue 18](https://github.com/tamnd/grh-lean-handbook/issues/18) (the public form of the original proof).

The register records what a reader must know to read the source with care. It does not say that the proof is correct. The source claims a proof of the five theorems, and Lean accepts it, if the reported checks hold.

Status: drafted by a model. No person has checked this chapter against the Lean source.
