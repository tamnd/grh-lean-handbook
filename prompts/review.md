# The brief for a checker of a chapter

You check one chapter of The GRH Lean Handbook against the Lean source at the commit in `EDITION`. A checker is a person. A model can help a person check, but a model cannot set the status `checked` or `reviewed`.

## What you check

For each section of the chapter:

1. Each `decls:` name exists at the pin. `ghb check` tests this.
2. Each statement matches its Lean type: the same objects, hypotheses, quantifiers and conclusion. A statement must not be stronger than the Lean statement, and it must not add a hypothesis. Open the file and the line of each name on the `Lean:` line, and compare.
3. Each object is defined before its use, in the chapter or by a link.
4. Each proof gives the main steps, and each step cites the result that it uses. The citations resolve. Read each proof against the Lean proof.
5. The remarks on the formalization name every unused hypothesis and every stated input in scope.
6. Each size and constant is explicit, and it matches the source.
7. The citations of the notes name a chapter, a section or a theorem number, and they are correct.
8. The style rules of `prompts/chapter.md` hold.
9. The build has no unresolved link and no overfull box.

## How you record the result

- If the chapter passes, set `status: checked` and `checked_by: <your name>` in the front matter of each section. Use your name, not a handle of a model.
- A person who works in the field and reads the chapter as mathematics sets `status: reviewed` and `reviewed_by: <name>`.
- If a point fails, open an issue with the file, the line, the Lean name and what is wrong. Do not raise the status. Fix the text in a pull request, or leave the issue for the writer.

## The report

List each section with its result: passed, or the issues that you opened. Give the time that you spent, and the names that you could not compare.
