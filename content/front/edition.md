---
title: About this edition
---
This is edition {{version}} of The GRH Lean Handbook, made on {{date}}. It explains the Lean source of lsernau/grh-lean at commit {{pin}}. The book is not a check of that source. It is a guide to the mathematics.

The book keeps three things apart.

1. **What Lean checks.** The source states five theorems in `Main.lean`. Lean accepts them if the build and the axiom check pass. The source reports these checks, but the repository has no logs of them. We did not run them again. A reader can run `lake build` and `scripts/PrintAxioms.lean` at the pin.
2. **What the source says.** The documents, the docstrings and the names are notes by the same author as the code. Lean checks none of them.
3. **What the book explains.** Each chapter explains the mathematics of one part of the source. Each chapter has a status: `drafted`, `checked` or `reviewed`. A model can set `drafted` only. A chapter is `checked` when a named person has compared each statement with its Lean type and read each proof against the Lean proof. A chapter is `reviewed` when a named person who works in the field has read it as mathematics.

The book does not say in its own voice that the proof is correct. It says what the source claims, what Lean accepts if the reported checks hold, and what each chapter explains. The status of each chapter is on its first page. Volume 0 has a table of all of them.
