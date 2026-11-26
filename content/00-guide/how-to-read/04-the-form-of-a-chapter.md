---
title: The form of a chapter
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The form of a chapter

Every chapter of the book has the same form. A reader who knows the form can find the statement, the proof, the example or the remark that the reader needs, and can tell which part of a page is mathematics and which part is a note on the Lean text. This section describes the parts of a chapter in the order in which they come, then the parts of a statement, then the numbers and the links. Its example is the zero reflection theorem, Theorem 2.5.5 of Volume 1, in Section 5 of [from the half-plane to the line](/chapter/half-plane-to-line/).

### The parts of a chapter

A chapter has 5,000 to 15,000 words, in sections of 800 to 3,000 words. Each section has a number, for example 2.5 for the fifth section of the second chapter of a volume. The parts come in this order.

1. **The opening section.** It says what the chapter proves and where the result is used. It gives the place of the chapter in the chain of Section 2 of this chapter, with a link to [the theorem and the plan](/chapter/theorem-and-plan/). It says what the chapter uses, and it gives a short sketch of the proof. It also names the points that need care. In the example, the opening section names three such points: the finite Euler factors, the poles of the gamma factor, and a convention of Mathlib for the gamma function at its poles.
2. **The sections of the argument**, in the order that a reader needs them. Each definition and lemma comes before its use, and the simple comes before the deep. This order can differ from the order of the files of the source.
3. **A model case** before a general case, where the argument is long. In the example the model case is the zeta function, in its own section, before the reflection for every Dirichlet character. Other chapters take one place, rank one, one twist, or a classical argument with the same idea: Liouville's inequality before the slope inequality, a one-term Landau lemma before the criterion.
4. **Examples**, where they help: a small case that can be computed, or a picture in words. An example has a numbered head, like a statement.
5. **Exercises**, 3 to 8 at the end of the chapter, each with a hint. They check the reading. Some ask the reader to compute a case. Some ask for a proof that the text leaves out. Some ask the reader to find where a hypothesis is used, or to find the Lean statement and compare it with the text.
6. **Notes and references.** The last section. It gives the classical sources of each main result, says how the treatment of the book differs from them, and says where to read further. A source is cited with a chapter, section or theorem number. When the book reports a citation of the source that it has not compared itself, it says so.

The status of the chapter is printed in a box on its first page, under the title. Section 5 explains it.

### A statement and its Lean line

A statement has a kind, a number, an optional name in parentheses, and a text. The kinds are Definition, Lemma, Proposition, Theorem, Corollary, Remark and Example. In the source of the book, the example looks like this.

```text
  **Theorem (Zero reflection).** Let $q \geq 1$, let $\chi$ be a
  Dirichlet character modulo $q$, and let $s \in \mathbb{C}$ with
  $\operatorname{Re} s \neq 0$, $s \neq 1$ and $L(s, \chi) = 0$.
  Then $G_\chi(s) = 0$ or $L(1 - s, \bar\chi) = 0$.

  Lean: `New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero`
  (Lib/Analytic/ZeroSymmetry.lean).
```

The build gives the statement its number. The number has three parts: the chapter, the section, and the place of the statement in the section. So Theorem 2.5.5 is the fifth statement of Section 5 of Chapter 2 of its volume. A link from another volume adds the volume: "Theorem 2.5.5 of Volume 1".

The text of a statement is mathematics, in the notation of [notation and conventions](/chapter/notation/). It says exactly what the Lean statement says: the same objects, the same hypotheses, the same quantifiers and the same conclusion. It does not make the conclusion stronger, and it does not add a hypothesis. In the example, the conclusion is a disjunction, because the Lean conclusion is a disjunction, and the hypothesis $\operatorname{Re} s \neq 0$ is there because the Lean statement has it. A textbook would state the functional equation of the completed L-function. The source keeps only the reflection of zeros, and so does the statement.

The line under the statement starts with `Lean:`. It names one declaration of the readable edition, with its full namespace, and the file of `grh/src` that contains it. This is the only place where a name of the source enters the text of a statement. A reader who skips the line loses nothing of the mathematics. A reader who checks the book opens the file, finds the name, and compares the type with the text. Some lines have other forms.

1. A name of Mathlib has `(Mathlib)` after it, or the line starts with `Mathlib:` in place of `Lean:`. The book uses Mathlib at the commit that the source pins.
2. A name of the compact edition of the source has `(grh-compact)` after it. [The two editions](/chapter/two-editions/) explains that edition.
3. A line can name a second declaration, a wrapper or a small lemma that the statement also covers. Not every declaration gets a statement of its own.

Each name on a `Lean:` line is tested by the build of the book: it must be a declaration of the source at the pinned commit. The build does not test that the text matches the type. That is the work of a person (Section 5).

### Proofs

A proof runs from *Proof.* to the mark $\square$. It gives the main steps and, for each step, the earlier result that it uses, with a link. It leaves out the steps that only rewrite. If the Lean proof only passes its hypotheses to an earlier result, the proof is one sentence with one link.

The proof is the book's account of the Lean proof. It follows the Lean proof in its steps and in the results it uses, so that a reader can read the two side by side. Where the source proves a step by a different argument from the textbook one, the book gives the argument of the source, and the notes give the textbook argument. In the example, the proof has five steps. Each step names one lemma or one formula: the primitive character that induces $\chi$, the nonvanishing of the finite Euler factors for $\operatorname{Re} s \neq 0$, the gamma factor of an induced character, the functional equation of Mathlib, and the change of level. After the proof a paragraph says where each hypothesis is used. Many chapters do this for their main theorems. It is the first thing to check when a hypothesis looks unnecessary.

A proof in Volume 1 or in an argument volume can use a result of a later volume. Then the result is stated in full in the chapter, as a numbered statement with its `Lean:` line, and its proof is a link to the chapter that proves it. A statement of this kind is not a hypothesis of the book. It is a statement of the source that a later chapter explains. Its status is the status of that later chapter.

### Remarks on the formalization

A remark with the head **Remark (Formalization).** is a note on the Lean text, not on the mathematics. A remark of this kind comes after a statement when one of the following holds.

1. The object of the source differs from the object of the literature. The remark gives both, says how they differ, and says why the argument does not need more. For example, the source can prove a special case of a classical theorem, or state a classical theorem as a hypothesis of its own theorems.
2. A junk value matters to the meaning of the statement. In Lean, $x/0 = 0$, a divergent series has the sum $0$, and a function such as $\Gamma$ has a value at its poles. A statement can be true for a reason that a textbook would not accept. The remark says when this happens.
3. An object is chosen by the axiom of choice, so that the statement holds for some object and no formula gives it.
4. A constant is allowed to be $0$, or a hypothesis is not used by the proof.

In the example, the remark after the theorem says that the source keeps only the reflection of zeros, not the orders of the zeros or the root number, and it reports the citation of the source. A remark with the head **Remark.** and no name is a remark on the mathematics.

Volume 1 alone has more than eighty remarks on the formalization. They are the parts of the book that a Lean reader should read first. [Reading the Lean](/chapter/reading-the-lean/) explains the conventions that they use.

### Other marks

**Quotations of the source.** A sentence of the source in quotation marks, with a file and a line, reports what the source says. The book does not endorse it. The documents and the comments of the source are notes by its authors, and Lean checks none of them.

**Links.** A link to a chapter gives the title of the chapter, or its number in the printed book. A link to a statement prints its kind and number, for example "Theorem 2.5.5". A link to a chapter that is not yet written prints only its words, with no number. A link of the form `lean:` goes to a line of a file of the source on GitHub, at the pinned commit. The book uses these rarely, in remarks.

**Sizes.** The argument is quantitative, and the book keeps every size explicit: $\sqrt{x} \leq m \leq 2\sqrt{x}$, $x^{10^6} \leq x_1$, and so on. A chapter that uses a size cites its definition in [the data and its sizes](/chapter/data-and-sizes/). The book does not write "a suitable constant" unless the source does.

**Diagrams.** The diagrams of the book are drawn in text, in a fixed-width font. An arrow points from a statement or a chapter to the one that uses it, unless the diagram says otherwise.

### How to read a chapter

A first reading takes the opening section, the statements, and the model case, and skips the proofs. A second reading takes the proofs, with the earlier results that they cite. The `Lean:` lines and the remarks on the formalization are for a third reading, or for a reader who checks the book. The exercises come after the second reading. Each one has a hint.
