# The brief for a writer of a chapter

You write one chapter of The GRH Lean Handbook. The book explains the Lean proof of the Generalized Riemann Hypothesis in [lsernau/grh-lean](https://github.com/lsernau/grh-lean) as mathematics. The source is the readable edition `grh/` at the commit in `EDITION`. Each file of `grh/src` has a module docstring at its head, and `grh/GUIDE.md` gives a map. Start from that map.

## What you get

- The entry of your chapter in `content/NN-volume/volume.yaml`: its id, its title, its plan, its research note and its source prefixes under `grh/src`.
- The research note named in `research:` (for example `b §2.3`), and the notes on the argument, the background and the findings of the plan.
- The pinned clone of the source at `../grh-lean`. Do not change it.

Read all of the Lean files of your chapter before you write: the heads, the statements, and the proofs of the results that you state.

## The reader and the writer

- The reader is a graduate student in number theory. The student knows algebraic number theory, the basic analytic theory of L-functions (as in Davenport, *Multiplicative Number Theory*), and some modular forms. The student does not read Lean.
- You write as an expert who teaches. The text reads like a chapter of a good textbook, such as Iwaniec and Kowalski, *Analytic Number Theory*, or Bump, *Automorphic Forms and Representations*.
- The text is mathematics. Outside the `Lean:` lines and the remarks on the formalization, do not mention the code.

## The files

A chapter is the folder `content/NN-volume/<id>/`, where `<id>` is the id in volume.yaml. Each section is one file `NN-<slug>.md`, in the order of the sections. A section has 800 to 3,000 words. A chapter has 5,000 to 15,000 words. Count words with `wc -w`. A chapter of more than 15,000 words is split into parts, and the parts are written in order.

Each file opens with front matter, and its text opens with a `##` heading:

```markdown
---
title: The one-sided bound
lean:
  - New/Reduction/OneSidedBound.lean
decls:
  - New.eventually_primeRemainder_le_rpow
status: drafted
drafted_by: writer@<model>
---
## The one-sided bound

<A paragraph: what this section proves, and where the result is used.>
```

- `lean:` lists the files of `grh/src` that the section explains.
- `decls:` lists the declarations that get a statement in the section.
- `status:` is `drafted`. A model sets `drafted` only. The status `checked` needs a named person in `checked_by`, and `reviewed` needs a named person in `reviewed_by`.
- The title of the chapter comes from volume.yaml. Do not write a `#` heading.

## Statements and proofs

- Write `**Theorem.**` or `**Theorem (Name).**`. The kinds are Definition, Lemma, Proposition, Theorem, Corollary, Remark and Example. The build adds the number, for example Theorem 4.2.3.
- Under each statement, write one line: ``Lean: `New.D.enough_forms` (New/Reduction/ShortAndEnough.lean).`` A name of Mathlib has `(Mathlib)` after it. A name of the compact edition has `(grh-compact)` after it. A statement that is a definition or theorem of Mathlib can have a line `Mathlib: ...` in place of the `Lean:` line. A classical statement that the source does not formalize has a line `Not in the source.` in its place, with one sentence on how the source avoids it or what it uses instead.
- Each statement says exactly what the Lean statement says: the same objects, hypotheses, quantifiers and conclusion. Do not make a conclusion stronger. Do not add a hypothesis. If the Lean form is a special case of a classical result, state the Lean form, and give the classical form in the notes.
- Then the proof, from `*Proof.*` to `$\square$`. Give the main steps and the earlier result that each step uses, with a link. Leave out steps that only rewrite. If the Lean proof only passes its hypotheses on, the proof is one sentence.
- A result of `Lib` that the argument uses is stated in its textbook form first, with a source (author, title, theorem number). Then a `**Remark (Formalization).**` says how the Lean form differs: a special case, a stated input, a hypothesis that is not used.
- Not every declaration gets a statement. A second name, a wrapper, a projection or a small lemma goes into the `Lean:` line or into a proof.

## Sizes and constants

The argument is quantitative. The source fixes explicit sizes, for example m in [√x, 2√x] and r in [x⁵, 3x⁵], and explicit scale inequalities. Keep them explicit. Cite the definition of each size in [the data and its sizes](/chapter/data-and-sizes/). Do not replace an explicit constant with "a suitable constant" unless the source does.

## The chapter has

1. An opening section: what the chapter proves, where it sits in the argument (a link to [the plan](/chapter/theorem-and-plan/)), what it uses, and a short sketch of the proof.
2. Sections in the order that a reader needs them: each definition and lemma before its use, from the simple to the deep. This order can differ from the order of the files.
3. Examples where they help: a small case, a computation, a picture in words.
4. Exercises at the end, 3 to 8, with hints. They check the reading: compute a small case, prove a lemma that the text leaves out, find where a hypothesis is used.
5. A last section `## Notes and references`: the classical sources of each main result, how this treatment differs, and where to read further. Cite only a source that you are sure of, with a chapter, section or theorem number. `REFERENCES.md` of the source says which citations were compared with their sources. Prefer those.

## Links

- To a statement of the handbook: `[Theorem](/decl/<Lean name>/)`. The build writes "Theorem 4.2.3".
- To a chapter: `[the enough forms](/chapter/enough-forms/)`, or to a section: `/chapter/<id>/#<heading-anchor>`.
- To a line of Lean, rarely, in a remark: `[MainInequality.lean](lean:New/Reduction/MainInequality.lean#L40)`. The build makes a link to GitHub at the pin.

A link to a chapter that is not written yet is a warning, not an error. A link to an unknown target fails the check.

## The style

- Use ASD-STE100 Simplified Technical English for all prose: short sentences, one idea in each, active voice, plain words.
- Do not use an em dash or an en dash. Do not break a line inside a sentence: one paragraph is one line.
- Do not use filler. The check rejects these words: "Moreover", "Furthermore", "It is worth noting", "Crucially", "delve", "notably", "leverage", "showcase", "powerful", "elegant", "seamless", "journey", "landscape", "tapestry", "realm", "intricate", "pivotal", "robust", "underscore".
- Write mathematics in LaTeX: `$...$` and `$$...$$`. Use standard notation, and define it at first use.
- Do not say that the proof is correct or that GRH is proved. Say "the source claims", "Lean accepts, if the reported checks hold", and "this chapter explains".

## Before you report

1. Run `python3 -m ghb check --volume N`. It must report 0 problems.
2. Build the volume: `python3 -m ghb build --volume N --formats pdf,epub --out /tmp/ghb-out`. Fix each overfull box. Delete `/tmp/ghb-out` after.
3. Report the sections, the words of each (`wc -w`), and each remark on the formalization that you added.

Two writers do not work on one chapter at once. Do not write in a chapter folder that another writer owns.
