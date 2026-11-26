---
title: Reading a statement against Mathlib
lean:
  - Statements.lean
  - Main.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Reading a statement against Mathlib

This chapter reads the statements of the source line by line. The source claims five theorems. Their types use one definition of Mathlib, `RiemannHypothesis`, and four propositions of the file Statements.lean. That file has 16 lines and imports only Mathlib. For each statement the chapter gives the Lean text, unfolds each definition of Mathlib that the text uses, and gives the classical statement that the text is meant to express. Where the Lean object and the classical object differ, a remark names the difference and says why it does not change the meaning. The last sections list what a reader must trust, and give exercises. The chapter uses nothing of the source except Statements.lean, Main.lean and the line of [the half-plane theorem](/decl/New.grh/). It uses Mathlib at the commit that the source pins, `56a005855ea17e0b0958f73ec801ae140b0a1679`.

### Why the statements need a chapter

A kernel check proves that a term has a type. It does not prove that the type says what a reader thinks it says. The source has about 300,000 lines of Lean. If the five types are faithful, then a reader who accepts the checks that the source reports does not have to read any of those lines to know what is claimed. If one type is wrong, the theorem can be true and say something else.

Here is a small case of the danger. Mathlib has two functions that a reader can call "the Dirichlet series of $\chi$". The first, `LSeries`, is the sum of the series where the series converges absolutely, and $0$ at every other point. The second, `DirichletCharacter.LFunction`, is the analytic continuation. Take a nonprincipal character $\chi$. Then the first function is $0$ at every $s$ with $0 < \operatorname{Re} s \leq 1$, because the series does not converge absolutely there. So the sentence "if $0 < \operatorname{Re} s < 1$ and the function vanishes at $s$, then $\operatorname{Re} s = 1/2$" is false for `LSeries`, at $s = 3/4$ for example. The same sentence for `LFunction` is the generalized Riemann hypothesis. The two sentences differ in one name. Section 4 makes this precise, and Exercise 4 asks the reader to prove it.

So a reader must read the definitions. This chapter does that for every name that the five types use.

### The method: pin a definition by theorems

The definitions of Mathlib are built for proofs, not for reading. Mathlib defines $\zeta$ through a Mellin transform of a theta function and a quotient by a gamma factor, and it defines $L(s, \chi)$ through Hurwitz zeta functions. A reader can follow each step of these constructions, and Sections 2 and 4 do so. But a reader does not have to. Two kinds of theorems of Mathlib fix each function on a large set.

1. A theorem that the function is equal to the classical Dirichlet series on the half-plane $\operatorname{Re} s > 1$, where the series converges absolutely.
2. A theorem that the function is complex differentiable at each point of a connected open set $U$ that contains this half-plane.

The identity theorem of complex analysis then says that the function is equal to the classical continuation at every point of $U$. Here $U$ is $\mathbb{C} \setminus \{1\}$, or $\mathbb{C}$ for a nonprincipal character. These theorems of Mathlib are proofs, and the kernel checks them like any other proof. The source reports that its export of the five theorems includes Mathlib, and that three independent checkers accept it (grh/README.md, line 28). This book did not rerun those checks ([the claim and its status](/chapter/claim-and-status/)).

What the theorems do not fix are the values at the points outside $U$. In this chapter there is one such point, $s = 1$, the pole. Lean has no partial functions, so Mathlib gives the function a value there. Such a value is a *junk value*: it has no classical meaning. The chapter computes the junk value of $\zeta$ at $1$ from the definitions, and it checks that each statement excludes the point.

### A short guide to the Lean of the statements

The statements use little Lean. Here is all of it. [Reading the Lean](/chapter/reading-the-lean/) gives more.

- `def X : Prop := P` defines a proposition with the name `X`. It proves nothing. `theorem t : X := p` says that the term `p` proves `X`.
- `∀ s : ℂ, P s` is "for every complex number $s$, $P(s)$". A binder `(_ : Q)` in a `∀` has no name, and it means the same as `Q →`.
- `P → Q` is "if $P$, then $Q$". A chain `P → Q → R` is "if $P$ and $Q$, then $R$".
- `¬`, `∃`, `∨` and `≠` are "not", "there is", "or" and "is not equal to".
- `s.re` is the real part of $s$. It is a real number.
- A numeral has the type that the context gives it. In `s.re = 1 / 2` the right side is the real number $0.5$, because `s.re` is real. It is not a division of natural numbers, which would give $0$.
- `(n : ℂ)` is the natural number $n$, seen as a complex number.
- `[NeZero N]` in a `∀` is a hypothesis in square brackets. It says $N \neq 0$. Lean finds a proof of it by instance search when a statement is applied. For a reader it is one more hypothesis.
- `χ.IsPrimitive` is `DirichletCharacter.IsPrimitive χ`. The dot notation finds the name in the namespace of the type of `χ`.

### The plan of the chapter

Section 2 reads the two forms of the Riemann hypothesis, Mathlib's `RiemannHypothesis` and the zeta statement of the source. It unfolds Mathlib's $\zeta$ and computes its values at $0$, at $1$ and at the trivial zeros. Section 3 reads Mathlib's Dirichlet characters: the principal character `1`, the change of level, the conductor and primitivity. Section 4 reads Mathlib's Dirichlet L-function. Section 5 reads the three statements about L-functions, and shows how the four propositions of the source relate to each other and to the classical statements. Section 6 states the five theorems and the half-plane theorem, with their Lean text. Section 7 lists what a reader must trust. Section 8 has exercises and notes.

The chapter states the theorems. It does not prove the half-plane theorem, which is the content of the whole book. The deduction of the other four theorems from it is in [from the half-plane to the line](/chapter/half-plane-to-line/). Lean accepts the five theorems, if the checks that the source reports hold. This chapter explains what they say.
